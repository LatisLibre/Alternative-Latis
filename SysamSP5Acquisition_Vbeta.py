# -*- coding: utf-8 -*-
"""
Sysam SP5 Acquisition - Version17

Modifications principales (par rapport aux versions précédentes) :
- Correction du binding F10 (évite NameError si le handler est défini après la création de la fenêtre).
- Implémentation améliorée de l'impression (choix d'imprimante, ouverture des paramètres et impression
  de toutes les courbes visibles de l'onglet actif) en mode "best-effort" multi-plateforme.
- Fonction "Copier" implémentée (copie la courbe active au presse-papiers en CSV ; menu Édition).
- Divers nettoyages mineurs.
"""
import pycanum.main as pycan
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.animation as animation
from scipy.optimize import curve_fit
import tkinter as tk
from tkinter import messagebox, filedialog, simpledialog, colorchooser
from tkinter import ttk
import sys as sys_module
import csv
import os
import re
import tempfile
import subprocess
import platform

from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk

# ---------------------------
# Basic utilities / startup
# ---------------------------

def close_program():
    """Ferme proprement la fenêtre Tkinter et termine le programme."""
    global root
    try:
        if root is not None:
            try:
                root.destroy()
            except Exception:
                pass
    finally:
        try:
            sys_module.exit(0)
        except Exception:
            pass

# ---------------------------
# Global configuration & state
# ---------------------------

class Config:
    FE = 5000.0
    DUREE = 0.02
    CALIBRE = 10.0
    N_POINTS = 100
    VOIE_ACQ = 0
    MODE_ACQUISITION = "Normal"
    MODE_DECLENCHEMENT = "Manuel"
    VOIE_TRIG = 0
    SEUIL = 0.0
    PENTE = "Montante"
    PRE_TRIG = 0
    PLOT_STYLE = "Points + Courbe"
    DEFAULT_Y_MARGIN = 1.1

sysam_interface = None
CALIBRE_AFFICHE = Config.CALIBRE
ALL_CURVES = []         # default curves for main tab
N_POINTS_OSCILLO = 1000
root = None

# UI variables (initialized in setup_main_window)
grandeur_physique_var = None
duree_var = None
superposition_var = None
plot_notebook = None
ALL_PLOT_WINDOWS = []
nb_points_var = None
calibre_var = None
voie_acq_var = None
fe_display_var = None
voie_trig_var = None
seuil_var = None
pente_var = None
pre_trig_var = None
menu_voie_trig = None
entry_seuil = None
menu_pente = None
entry_pre_trig = None
label_voie_trig = None
label_seuil = None
label_pente = None
label_pre_trig = None
mode_declenchement_var = None
mode_acquisition_var = None
plot_style_var = None

CALCULATED_CURVES = []

# ---------------------------
# Reticule (crosshair) class
# ---------------------------

class Reticule:
    def __init__(self, ax, fig, canvas, curves_data, calibre):
        self.ax = ax
        self.fig = fig
        self.canvas = canvas
        self.curves_data = curves_data
        self.calibre = calibre
        self.active_curve_index = 0  # fixed to 0 by default; no dialog to change it

        self.coord_text = ax.text(0.5, 1.05, '',
                                  transform=ax.transAxes,
                                  ha='center', fontsize=10, visible=False)
        self.v_line = ax.axvline(x=0, color='r', linestyle='--', linewidth=0.8, visible=False)
        self.h_line = ax.axhline(y=0, color='b', linestyle='--', linewidth=0.8, visible=False)
        try:
            self.cid_move = self.canvas.mpl_connect('motion_notify_event', self.on_mouse_move)
        except Exception:
            self.cid_move = None

    def on_mouse_move(self, event):
        if event.inaxes == self.ax and event.xdata is not None and self.curves_data:
            x = event.xdata
            try:
                t_main, v_main, base_name, _ = self.curves_data[self.active_curve_index]
            except Exception:
                self.active_curve_index = 0
                if not self.curves_data or len(self.curves_data[0][0]) == 0:
                    self.hide_reticule()
                    return
                t_main, v_main, base_name, _ = self.curves_data[self.active_curve_index]

            if len(t_main) == 0:
                self.hide_reticule()
                return

            idx = np.argmin(np.abs(t_main - x))
            t_point = t_main[idx]
            v_point = v_main[idx]

            self.v_line.set_xdata(t_point)
            self.h_line.set_ydata(v_point)

            grandeur_label = base_name.split('(')[0].strip() or "Grandeur"
            coord_str = f"Réticule sur {grandeur_label}: T={t_point:.4f} s, Y={v_point:.3f}"
            self.coord_text.set_text(coord_str)
            self.show_reticule()
            if self.fig and self.fig.canvas:
                self.fig.canvas.draw_idle()
        else:
            self.hide_reticule()

    def show_reticule(self):
        if not self.v_line.get_visible():
            self.v_line.set_visible(True)
            self.h_line.set_visible(True)
            self.coord_text.set_visible(True)

    def hide_reticule(self):
        if self.v_line.get_visible():
            self.v_line.set_visible(False)
            self.h_line.set_visible(False)
            self.coord_text.set_visible(False)
            self.coord_text.set_text('')
            if self.fig and self.fig.canvas:
                self.fig.canvas.draw_idle()

# ---------------------------
# Helpers: names, flags, colors
# ---------------------------

def _extract_unit_from_name(name):
    if not name or '(' not in name or ')' not in name:
        return None
    try:
        unit = name.split('(')[-1].replace(')', '').strip()
        return unit
    except Exception:
        return None

def _sync_visible_flags(window_data):
    curves = window_data.get('curves_data', [])
    flags = window_data.get('visible_flags', [])
    n = len(curves)
    if len(flags) < n:
        flags.extend([True] * (n - len(flags)))
    elif len(flags) > n:
        flags = flags[:n]
    window_data['visible_flags'] = flags

def _sync_curve_colors(window_data):
    """Ensure window_data['curve_colors'] matches number of curves (None = default)."""
    curves = window_data.get('curves_data', [])
    colors = window_data.get('curve_colors', [])
    n = len(curves)
    if len(colors) < n:
        colors.extend([None] * (n - len(colors)))
    elif len(colors) > n:
        colors = colors[:n]
    window_data['curve_colors'] = colors

def get_active_plot_window():
    global plot_notebook, ALL_PLOT_WINDOWS
    if not plot_notebook or not ALL_PLOT_WINDOWS:
        return None
    selected_tab_id = plot_notebook.select()
    selected_frame = plot_notebook.nametowidget(selected_tab_id)
    for window in ALL_PLOT_WINDOWS:
        if window['frame'] == selected_frame:
            return window
    if ALL_PLOT_WINDOWS:
        return ALL_PLOT_WINDOWS[0]
    return None

# ---------------------------
# Printing helpers (improved)
# ---------------------------

def _get_system_printers():
    """
    Retourne une liste de noms d'imprimantes disponibles sur le système.
    Utilise win32print si disponible ; sinon tente lpstat (Unix), sinon retourne [].
    """
    printers = []
    # Try win32print first (Windows / pywin32)
    try:
        import win32print
        try:
            flags = win32print.PRINTER_ENUM_LOCAL | win32print.PRINTER_ENUM_CONNECTIONS
            raw = win32print.EnumPrinters(flags)
            printers = [p[2] for p in raw if p and len(p) > 2]
        except Exception:
            printers = []
    except Exception:
        # Not on Windows or pywin32 missing: try lpstat (common on Unix with CUPS)
        try:
            out = subprocess.check_output(['lpstat', '-a'], stderr=subprocess.DEVNULL).decode('utf-8', errors='ignore')
            lines = [ln.strip() for ln in out.splitlines() if ln.strip()]
            printers = [ln.split()[0] for ln in lines if ln]
            printers = list(dict.fromkeys(printers))  # unique preserving order
        except Exception:
            printers = []
    return printers

def _open_printer_settings(printer_name):
    """
    Ouvre le dialogue des propriétés/réglages de l'imprimante choisie si possible.
    Sous Windows utilise printui.dll, sous Linux tente system-config-printer / lpoptions,
    sous macOS ouvre le panneau Printers & Scanners.
    """
    system = platform.system()
    try:
        if system == 'Windows':
            cmd = ['rundll32', 'printui.dll,PrintUIEntry', '/p', '/n', printer_name]
            subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            return True
        elif system == 'Darwin':
            try:
                subprocess.Popen(['open', '/System/Library/PreferencePanes/PrintAndScan.prefPane'])
                return True
            except Exception:
                return False
        else:
            try:
                subprocess.Popen(['system-config-printer', '--modify-printer', printer_name], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                return True
            except Exception:
                try:
                    out = subprocess.check_output(['lpoptions', '-p', printer_name, '-l'], stderr=subprocess.DEVNULL).decode('utf-8', errors='ignore')
                    dlg = tk.Toplevel(root)
                    dlg.title(f"Options imprimante: {printer_name}")
                    text = tk.Text(dlg, wrap='word', width=80, height=30)
                    text.insert('1.0', out)
                    text.config(state='disabled')
                    text.pack(fill='both', expand=True)
                    tk.Button(dlg, text="Fermer", command=dlg.destroy).pack(pady=6)
                    return True
                except Exception:
                    return False
    except Exception:
        return False

def _print_file_to_printer(file_path, printer_name=None):
    """
    Envoie le fichier image au système d'impression.
    - Sur Unix-like : lpr -P printer file  ou lp -d printer file
    - Sur macOS : lp -d printer file
    - Sur Windows : os.startfile(file, 'print') (utilise imprimante par défaut)
    Returns True if a print command was dispatched, False otherwise.
    """
    system = platform.system()
    try:
        if system == 'Windows':
            try:
                os.startfile(file_path, "print")
                return True
            except Exception:
                return False
        elif system == 'Darwin':
            if printer_name:
                cmd = ['lp', '-d', printer_name, file_path]
            else:
                cmd = ['lp', file_path]
            subprocess.run(cmd, check=True)
            return True
        else:
            if printer_name:
                try:
                    cmd = ['lpr', '-P', printer_name, file_path]
                    subprocess.run(cmd, check=True)
                    return True
                except Exception:
                    try:
                        cmd = ['lp', '-d', printer_name, file_path]
                        subprocess.run(cmd, check=True)
                        return True
                    except Exception:
                        pass
            try:
                subprocess.run(['lpr', file_path], check=True)
                return True
            except Exception:
                try:
                    subprocess.run(['lp', file_path], check=True)
                    return True
                except Exception:
                    return False
    except Exception:
        return False

# ---------------------------
# Plot creation and tabs
# ---------------------------

def create_plot_in_frame(parent_frame, curves_data, title="Fenêtre Graphique", y_label="Tension (V)"):
    fig, ax = plt.subplots(figsize=(6, 4), dpi=100)
    ax.set_title(title)
    ax.set_xlabel("Temps (s)")
    ax.set_ylabel(y_label)
    ax.set_xlim(0, Config.DUREE)
    ax.set_ylim(-CALIBRE_AFFICHE * Config.DEFAULT_Y_MARGIN, CALIBRE_AFFICHE * Config.DEFAULT_Y_MARGIN)
    ax.grid(True)

    canvas = FigureCanvasTkAgg(fig, master=parent_frame)
    canvas_widget = canvas.get_tk_widget()
    canvas_widget.pack(side=tk.TOP, fill=tk.BOTH, expand=1)

    toolbar = NavigationToolbar2Tk(canvas, parent_frame)
    toolbar.update()
    canvas.draw()

    reticule = Reticule(ax, fig, canvas, curves_data, CALIBRE_AFFICHE)

    x_lim_init = ax.get_xlim()
    y_lim_init = ax.get_ylim()

    window_data = {
        'frame': parent_frame,
        'fig': fig,
        'ax': ax,
        'canvas': canvas,
        'toolbar': toolbar,
        'reticule': reticule,
        'curves_data': curves_data,
        '_previous_x_limits': x_lim_init,
        '_previous_y_limits': y_lim_init,
        '_initial_x_limits': x_lim_init,
        '_initial_y_limits': y_lim_init,
        'secax': None,
        'sec_color': 'tab:red',
        'removed_curves': [],
        'visible_flags': [],
        'curve_colors': []   # optional user-chosen colors
    }

    # popup menu (clic droit)
    popup_menu = tk.Menu(canvas_widget, tearoff=0)
    popup_menu.add_command(label="Calibrage Auto (Optimiser l'Affichage)", command=lambda wd=window_data: auto_calibrate_plot(wd))
    popup_menu.add_command(label="Décalibrer (Retour affichage initial)", command=lambda wd=window_data: de_calibrate_plot(wd))
    popup_menu.add_separator()
    style_menu = tk.Menu(popup_menu, tearoff=0)
    style_options = ["Points", "Courbe seule", "Points + Courbe"]
    for style in style_options:
        style_menu.add_radiobutton(label=style, command=lambda s=style, wd=window_data: update_plot_style(style=s, window_data=wd))
    popup_menu.add_cascade(label="Style d'Affichage", menu=style_menu)
    canvas_widget.bind("<Button-3>", lambda event: popup_menu.post(event.x_root, event.y_root))

    return window_data

def open_new_plot_window_tab(curves_to_plot=None, title_suffix=""):
    global plot_notebook, ALL_PLOT_WINDOWS
    if plot_notebook is None:
        return None
    new_tab_frame = tk.Frame(plot_notebook)
    new_curves_list = curves_to_plot if curves_to_plot is not None else []
    y_label = new_curves_list[0][2] if new_curves_list and "Temps" not in new_curves_list[0][2] else (grandeur_physique_var.get() if grandeur_physique_var else "Grandeur")
    window_data = create_plot_in_frame(new_tab_frame, new_curves_list,
                                       title=f"Nouvelle Fenêtre {len(ALL_PLOT_WINDOWS) + 1} {title_suffix}",
                                       y_label=y_label)
    ALL_PLOT_WINDOWS.append(window_data)
    tab_name = f"Fenêtre {len(ALL_PLOT_WINDOWS)}"
    plot_notebook.add(new_tab_frame, text=tab_name)
    plot_notebook.select(new_tab_frame)
    plot_mode_unique(window_data)
    if new_curves_list:
        auto_calibrate_plot(window_data)
    return window_data

def create_initial_plot_notebook(parent_frame):
    global plot_notebook, ALL_PLOT_WINDOWS
    plot_notebook = ttk.Notebook(parent_frame)
    plot_notebook.pack(side=tk.TOP, fill=tk.BOTH, expand=1)
    main_tab_frame = tk.Frame(plot_notebook)
    plot_notebook.add(main_tab_frame, text="Fenêtre 1 (Principale)")
    initial_window = create_plot_in_frame(main_tab_frame, ALL_CURVES,
                                          title="Acquisition Normal (Bloc) - Principale",
                                          y_label=(grandeur_physique_var.get() if grandeur_physique_var else "Grandeur"))
    ALL_PLOT_WINDOWS.append(initial_window)

# ---------------------------
# Curve management functions
# ---------------------------

def remove_curve(window_data, idx):
    try:
        curve = window_data['curves_data'].pop(idx)
        if 'visible_flags' in window_data and idx < len(window_data['visible_flags']):
            window_data['visible_flags'].pop(idx)
        if 'curve_colors' in window_data and idx < len(window_data['curve_colors']):
            window_data['curve_colors'].pop(idx)
        window_data.setdefault('removed_curves', []).append(curve)
        if window_data['reticule'].active_curve_index >= len(window_data['curves_data']):
            window_data['reticule'].active_curve_index = 0
        plot_mode_unique(window_data)
    except Exception as e:
        messagebox.showerror("Suppression", f"Impossible de supprimer la courbe: {e}")

def restore_curve(window_data, removed_index):
    try:
        removed = window_data.get('removed_curves', [])
        if not removed or removed_index < 0 or removed_index >= len(removed):
            return
        curve = removed.pop(removed_index)
        window_data['curves_data'].append(curve)
        _sync_visible_flags(window_data)
        _sync_curve_colors(window_data)
        plot_mode_unique(window_data)
    except Exception as e:
        messagebox.showerror("Restauration", f"Impossible de restaurer la courbe: {e}")

def manage_curves_dialog(window_data=None):
    if window_data is None:
        window_data = get_active_plot_window()
    if window_data is None:
        messagebox.showwarning("Gérer les courbes", "Aucun onglet actif.")
        return
    _sync_visible_flags(window_data)
    curves = window_data['curves_data']
    removed = window_data.get('removed_curves', [])
    dlg = tk.Toplevel(root)
    dlg.title("Gérer les courbes")
    dlg.geometry("640x420")
    dlg.transient(root)

    top_frame = ttk.LabelFrame(dlg, text="Courbes actives")
    top_frame.pack(fill='both', expand=True, padx=8, pady=6)

    canvas_frame = tk.Canvas(top_frame)
    scrollbar = ttk.Scrollbar(top_frame, orient="vertical", command=canvas_frame.yview)
    scrollable = ttk.Frame(canvas_frame)
    scrollable.bind("<Configure>", lambda e: canvas_frame.configure(scrollregion=canvas_frame.bbox("all")))
    canvas_frame.create_window((0,0), window=scrollable, anchor="nw")
    canvas_frame.configure(yscrollcommand=scrollbar.set)
    canvas_frame.pack(side="left", fill="both", expand=True)
    scrollbar.pack(side="right", fill="y")

    temp_vars = []
    for i, (t, v, nom, is_raw) in enumerate(curves):
        row = ttk.Frame(scrollable)
        row.pack(fill='x', padx=4, pady=2)
        var = tk.IntVar(value=1 if window_data['visible_flags'][i] else 0)
        temp_vars.append(var)
        def make_toggle(i_local, var_local):
            def toggle():
                window_data['visible_flags'][i_local] = bool(var_local.get())
                plot_mode_unique(window_data)
            return toggle
        cb = tk.Checkbutton(row, text=f"[{i+1}] {nom}", variable=var, command=make_toggle(i, var))
        cb.pack(side='left', anchor='w', padx=2)
        def make_remove(i_local):
            def _remove():
                if messagebox.askyesno("Supprimer", f"Supprimer la courbe '{curves[i_local][2]}' (déplacée dans 'Supprimées') ?"):
                    remove_curve(window_data, i_local)
                    dlg.destroy()
                    root.after(50, lambda: manage_curves_dialog(window_data))
            return _remove
        ttk.Button(row, text="Supprimer", command=make_remove(i)).pack(side='right', padx=4)

    bottom_frame = ttk.LabelFrame(dlg, text="Courbes supprimées (restaurer)")
    bottom_frame.pack(fill='x', padx=8, pady=6)
    removed_listbox = tk.Listbox(bottom_frame, height=6)
    removed_listbox.pack(side='left', fill='x', expand=True, padx=4, pady=4)
    for r in removed:
        removed_listbox.insert(tk.END, r[2])

    def on_restore():
        sel = removed_listbox.curselection()
        if not sel:
            messagebox.showwarning("Restauration", "Sélectionnez une courbe supprimée à restaurer.")
            return
        idx = sel[0]
        restore_curve(window_data, idx)
        dlg.destroy()
        root.after(50, lambda: manage_curves_dialog(window_data))

    ttk.Button(bottom_frame, text="Restaurer la sélection", command=on_restore).pack(side='right', padx=6, pady=6)

    def close_and_apply():
        _sync_visible_flags(window_data)
        dlg.destroy()

    ttk.Button(dlg, text="Fermer", command=close_and_apply).pack(side='bottom', pady=6)
    dlg.grab_set()
    dlg.focus_force()
    dlg.wait_window()

# ---------------------------
# Data table functions (with integrated spreadsheet)
# ---------------------------

def open_data_table():
    active_window = get_active_plot_window()
    if not active_window or not active_window['curves_data']:
        messagebox.showwarning("Tableau", "Aucune courbe n'a été acquise ou chargée dans l'onglet actif.")
        return
    selected = select_curve_dialog(active_window, title="Sélection de la courbe pour le Tableau")
    if selected is None:
        return
    curve_index, _, _, _, _ = selected
    _show_data_table_for_curve(active_window, curve_index)

def _show_data_table_for_curve(active_window, curve_index):
    """
    Ouvre une fenêtre tableau de la courbe sélectionnée.
    Ajout : bouton "Feuille de calcul" pour créer de nouvelles colonnes via formules basées sur t et y.
    """
    try:
        t_arr, v_arr, curve_name, is_raw = active_window['curves_data'][curve_index]
    except Exception as e:
        messagebox.showerror("Tableau", f"Impossible de récupérer la courbe : {e}")
        return

    # Convert to Python lists for easy editing in Treeview
    t_list = list(t_arr.tolist()) if isinstance(t_arr, np.ndarray) else list(t_arr)
    v_list = list(v_arr.tolist()) if isinstance(v_arr, np.ndarray) else list(v_arr)

    tbl_win = tk.Toplevel(root)
    tbl_win.title(f"Tableau des valeurs - {curve_name}")
    tbl_win.geometry("900x520")
    tbl_win.transient(root)

    header = tk.Frame(tbl_win)
    header.pack(fill='x', padx=8, pady=4)
    tk.Label(header, text=f"Courbe : {curve_name}", font=('Helvetica', 10, 'bold')).pack(side='left')
    tk.Label(header, text=f"Points : {len(t_list)}", fg='gray40').pack(side='right')

    frame = tk.Frame(tbl_win)
    frame.pack(fill='both', expand=True, padx=8, pady=4)
    # columns: time + value + any computed columns (dynamically added)
    columns = ['time', 'value']
    tree = ttk.Treeview(frame, columns=columns, show='headings', selectmode='browse')
    tree.heading('time', text='Temps (s)')
    tree.heading('value', text=curve_name)
    vsb = ttk.Scrollbar(frame, orient="vertical", command=tree.yview)
    hsb = ttk.Scrollbar(frame, orient="horizontal", command=tree.xview)
    tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
    tree.grid(row=0, column=0, sticky='nsew')
    vsb.grid(row=0, column=1, sticky='ns')
    hsb.grid(row=1, column=0, sticky='ew')
    frame.grid_rowconfigure(0, weight=1)
    frame.grid_columnconfigure(0, weight=1)

    # store computed column names and values
    computed_columns = []  # list of dicts: {'id': col_id, 'name': display_name, 'values': list_of_values, 'unit': unit}

    def refresh_treeview():
        # rebuild columns
        all_columns = ['time', 'value'] + [c['id'] for c in computed_columns]
        tree.config(columns=all_columns)
        tree.heading('time', text='Temps (s)')
        tree.heading('value', text=curve_name)
        for c in computed_columns:
            tree.heading(c['id'], text=c['name'])
        # remove all items then reinsert
        for iid in tree.get_children():
            tree.delete(iid)
        n = max(len(t_list), len(v_list), *(len(c['values']) for c in computed_columns) if computed_columns else [0])
        for i in range(n):
            ti = f"{t_list[i]:.6f}" if i < len(t_list) else ""
            vi = f"{v_list[i]:.6f}" if i < len(v_list) else ""
            row = [ti, vi]
            for c in computed_columns:
                val = c['values'][i] if i < len(c['values']) else ""
                if val != "":
                    try:
                        row.append(f"{float(val):.6f}")
                    except Exception:
                        row.append(str(val))
                else:
                    row.append("")
            tree.insert('', 'end', iid=str(i), values=row)

    # initial fill
    refresh_treeview()

    edit_info = {'entry': None}

    def on_double_click(event):
        region = tree.identify('region', event.x, event.y)
        if region != 'cell':
            return
        row_id = tree.identify_row(event.y)
        col = tree.identify_column(event.x)  # like '#1', '#2', ...
        if not row_id:
            return
        bbox = tree.bbox(row_id, col)
        if not bbox:
            return
        x, y, width, height = bbox
        if edit_info['entry'] is not None:
            edit_info['entry'].destroy()
            edit_info['entry'] = None

        col_index = int(col.replace('#', '')) - 1  # 0-based
        def save_edit(event=None):
            new_val = entry.get().strip()
            try:
                newf = float(new_val.replace(',', '.'))
                is_num = True
            except Exception:
                is_num = False
            idx = int(row_id)
            if col_index == 0:
                # time edited
                if not is_num:
                    messagebox.showwarning("Édition", "Temps non valide. Saisissez un nombre.")
                    entry.focus_set()
                    return
                t_list[idx] = newf
                tree.set(row_id, 'time', f"{newf:.6f}")
            elif col_index == 1:
                # value edited
                if not is_num:
                    messagebox.showwarning("Édition", "Valeur non valide. Saisissez un nombre.")
                    entry.focus_set()
                    return
                v_list[idx] = newf
                tree.set(row_id, 'value', f"{newf:.6f}")
            else:
                # computed column
                cidx = col_index - 2
                if cidx >= 0 and cidx < len(computed_columns):
                    if not is_num:
                        # allow empty / text?
                        computed_columns[cidx]['values'][idx] = new_val
                        tree.set(row_id, computed_columns[cidx]['id'], new_val)
                    else:
                        computed_columns[cidx]['values'][idx] = newf
                        tree.set(row_id, computed_columns[cidx]['id'], f"{newf:.6f}")
            try:
                # update underlying curve if time/value were edited
                active_window['curves_data'][curve_index] = (np.array(t_list), np.array(v_list), curve_name, is_raw)
            except Exception:
                pass
            try:
                plot_mode_unique(active_window)
                auto_calibrate_plot(active_window)
            except Exception:
                pass
            entry.destroy()
            edit_info['entry'] = None

        entry = tk.Entry(tree)
        entry.place(x=x, y=y, width=width, height=height)
        current_val = tree.set(row_id, column=tree['columns'][col_index])
        entry.insert(0, current_val)
        entry.focus_set()
        entry.bind("<Return>", save_edit)
        entry.bind("<FocusOut>", save_edit)
        edit_info['entry'] = entry

    tree.bind('<Double-1>', on_double_click)

    # Buttons frame (Export, Calcul, Close)
    btn_frame = tk.Frame(tbl_win)
    btn_frame.pack(fill='x', padx=8, pady=6)

    def close_tbl():
        try:
            active_window['curves_data'][curve_index] = (np.array(t_list), np.array(v_list), curve_name, is_raw)
            plot_mode_unique(active_window)
            auto_calibrate_plot(active_window)
        except Exception:
            pass
        tbl_win.destroy()

    def export_table_csv():
        try:
            fname = filedialog.asksaveasfilename(defaultextension=".csv",
                                                 filetypes=[("CSV files", "*.csv")],
                                                 title="Exporter le tableau complet")
            if not fname:
                return
            with open(fname, 'w', newline='', encoding='utf-8') as f:
                writer = csv.writer(f, delimiter=';')
                # headers
                headers = ['Temps (s)', curve_name]
                for c in computed_columns:
                    headers.append(c['name'])
                writer.writerow(headers)
                n = max(len(t_list), len(v_list), *(len(c['values']) for c in computed_columns) if computed_columns else [0])
                for i in range(n):
                    row = []
                    row.append(f"{t_list[i]:.6f}" if i < len(t_list) else "")
                    row.append(f"{v_list[i]:.6f}" if i < len(v_list) else "")
                    for c in computed_columns:
                        val = c['values'][i] if i < len(c['values']) else ""
                        if isinstance(val, (int, float)):
                            row.append(f"{val:.6f}")
                        else:
                            row.append(str(val) if val != "" else "")
                    writer.writerow(row)
            messagebox.showinfo("Export", f"Tableau exporté : {os.path.basename(fname)}")
        except Exception as e:
            messagebox.showerror("Export", f"Erreur lors de l'export : {e}")

    # --- New: Inline calculation dialog ---
    def open_inline_calcul():
        """
        Ouvre une boîte de dialogue qui permet d'entrer une formule basée sur :
         - t : tableau temps (numpy array)
         - y : tableau valeurs (numpy array)
        La formule est évaluée en environnement sécurisé (np exposé).
        Le résultat (np.array) est ajouté comme nouvelle colonne dans le tableau et
        peut être (optionnel) ajouté comme nouvelle courbe dans l'onglet actif.
        """
        calc_win = tk.Toplevel(tbl_win)
        calc_win.title("Feuille de calcul (tableau courant)")
        calc_win.geometry("520x320")
        calc_win.transient(tbl_win)

        frm = ttk.Frame(calc_win, padding=10)
        frm.pack(fill='both', expand=True)

        tk.Label(frm, text="Créer une nouvelle grandeur à partir de la courbe sélectionnée", font=('Helvetica', 11, 'bold')).pack(anchor='w', pady=(0,6))

        info = ("Variables disponibles dans la formule :\n"
                "  - t : vecteur temps (numpy array)\n"
                "  - y : vecteur valeurs (numpy array)\n"
                "Exemples : np.gradient(y,t), y*2, np.sin(2*np.pi*50*t), (y - np.mean(y)) / np.std(y)")
        tk.Label(frm, text=info, justify='left', fg='darkgreen').pack(anchor='w', pady=4)

        entry_frame = ttk.Frame(frm)
        entry_frame.pack(fill='x', pady=6)
        tk.Label(entry_frame, text="Nom de la nouvelle colonne:").grid(row=0, column=0, sticky='w', padx=4, pady=2)
        new_name_var = tk.StringVar(value="Grandeur_Calculee")
        tk.Entry(entry_frame, textvariable=new_name_var, width=30).grid(row=0, column=1, padx=4, pady=2)
        tk.Label(entry_frame, text="Unité:").grid(row=1, column=0, sticky='w', padx=4, pady=2)
        new_unit_var = tk.StringVar(value="")
        tk.Entry(entry_frame, textvariable=new_unit_var, width=12).grid(row=1, column=1, sticky='w', padx=4, pady=2)

        tk.Label(entry_frame, text="Formule (Python, utiliser np):").grid(row=2, column=0, sticky='w', padx=4, pady=6)
        formula_var = tk.StringVar(value="")  # empty by default
        formula_entry = tk.Entry(entry_frame, textvariable=formula_var, width=60)
        formula_entry.grid(row=2, column=1, padx=4, pady=2)

        add_curve_var = tk.BooleanVar(value=False)
        tk.Checkbutton(frm, text="Ajouter le résultat comme nouvelle courbe dans l'onglet actif", variable=add_curve_var).pack(anchor='w', pady=6)

        results_label = tk.StringVar(value="")
        tk.Label(frm, textvariable=results_label, fg='blue').pack(anchor='w', pady=4)

        def run_calculation():
            name = new_name_var.get().strip()
            unit = new_unit_var.get().strip()
            formula = formula_var.get().strip()
            if not name or not formula:
                messagebox.showwarning("Calcul", "Veuillez fournir un nom et une formule.")
                return
            # prepare environment
            try:
                t_np = np.array(t_list)
                y_np = np.array(v_list)
            except Exception as e:
                messagebox.showerror("Calcul", f"Erreur préparation des données : {e}")
                return
            eval_env = {'np': np, 't': t_np, 'y': y_np}
            # safety checks
            if re.search(r'\b(os|sys|file|exec|eval|import|open|__|subprocess)\b', formula):
                messagebox.showerror("Calcul", "La formule contient des termes interdits pour des raisons de sécurité.")
                return
            try:
                result = eval(formula, {"__builtins__": None}, eval_env)
            except Exception as e:
                messagebox.showerror("Calcul", f"Erreur lors de l'évaluation de la formule : {e}")
                return
            # convert scalar to array if needed
            if isinstance(result, (int, float)):
                result = np.full_like(t_np, result, dtype=float)
            if isinstance(result, np.ndarray):
                if result.shape != t_np.shape:
                    messagebox.showerror("Calcul", f"Le résultat a une taille {result.shape} différente de la taille du temps {t_np.shape}.")
                    return
                # add computed column
                comp_vals = result.tolist()
            else:
                # try to coerce list-like
                try:
                    comp_vals = list(result)
                    if len(comp_vals) != len(t_np):
                        messagebox.showerror("Calcul", "Le résultat n'a pas la bonne dimension.")
                        return
                except Exception:
                    messagebox.showerror("Calcul", "Le résultat de la formule n'est pas exploitable.")
                    return

            col_id = f"calc_{len(computed_columns)+1}"
            display_name = f"{name} ({unit})" if unit else name
            computed_columns.append({'id': col_id, 'name': display_name, 'values': comp_vals, 'unit': unit})
            refresh_treeview()
            results_label.set(f"Colonne '{display_name}' ajoutée ({len(comp_vals)} valeurs).")
            # optionally add curve
            if add_curve_var.get():
                # Append as new curve in active window
                try:
                    new_curve_name = display_name
                    active_window['curves_data'].append((np.array(t_list), np.array(comp_vals), new_curve_name, False))
                    results_label.set(results_label.get() + f" Courbe '{new_curve_name}' ajoutée.")
                    plot_mode_unique(active_window)
                    auto_calibrate_plot(active_window)
                except Exception as e:
                    messagebox.showwarning("Ajout courbe", f"Impossible d'ajouter la courbe au graphe: {e}")
            # keep dialog open for multiple formulas
        ttk.Button(frm, text="Calculer et Ajouter Colonne", command=run_calculation).pack(side='left', padx=6, pady=8)
        ttk.Button(frm, text="Fermer", command=calc_win.destroy).pack(side='right', padx=6, pady=8)

        calc_win.grab_set()
        calc_win.focus_force()
        calc_win.wait_window()

    # Buttons
    tk.Button(btn_frame, text="Feuille de calcul", command=open_inline_calcul).pack(side='left', padx=4)
    tk.Button(btn_frame, text="Exporter CSV", command=export_table_csv).pack(side='left', padx=4)
    tk.Button(btn_frame, text="Fermer", command=close_tbl).pack(side='right', padx=4)

    tbl_win.update_idletasks()
    w = tbl_win.winfo_width()
    h = tbl_win.winfo_height()
    x = (tbl_win.winfo_screenwidth() // 2) - (w // 2)
    y = (tbl_win.winfo_screenheight() // 2) - (h // 2)
    tbl_win.geometry(f'{w}x{h}+{x}+{y}')
    tbl_win.transient(root)
    tbl_win.grab_set()
    tbl_win.focus_force()
    return

# ---------------------------
# Calculation sheet (Feuille de calcul globale)
# ---------------------------

def open_calcul_sheet():
    """Feuille de calcul pour créer nouvelles grandeurs à partir des courbes présentes."""
    global CALCULATED_CURVES
    active_window = get_active_plot_window()
    if not active_window:
        messagebox.showwarning("Erreur", "Veuillez d'abord effectuer une acquisition ou charger des données.")
        return
    available_data = {}
    if active_window['curves_data']:
        base_t_data = active_window['curves_data'][0][0]
        available_data['t'] = (base_t_data, "s")
    else:
        messagebox.showwarning("Erreur", "Aucune donnée de base (Temps) trouvée dans l'onglet actif.")
        return
    base_time_length = len(available_data['t'][0])
    for t_data, v_data, name, _ in active_window['curves_data']:
        var_name = name.split('(')[0].strip().replace(' ', '_').replace('-', '_')
        unit = name.split('(')[-1].replace(')', '').strip() if '(' in name else "V"
        if len(v_data) == base_time_length:
            if var_name not in available_data:
                available_data[var_name] = (v_data, unit)
            else:
                i = 1
                temp_name = var_name
                while temp_name in available_data:
                    i += 1
                    temp_name = f"{var_name}_{i}"
                available_data[temp_name] = (v_data, unit)
    if not available_data or len(available_data) == 1:
        messagebox.showwarning("Erreur", "Aucune grandeur mesurée/importée dans l'onglet actif pour effectuer des calculs.")
        return
    calcul_window = tk.Toplevel(root)
    calcul_window.title("Feuille de calcul (Nouvelles Grandeurs)")
    header_frame = ttk.Frame(calcul_window)
    header_frame.pack(fill='x', padx=10, pady=5)
    tk.Label(header_frame, text="Création de nouvelles grandeurs :", font='Helvetica 10 bold').pack(anchor='w')
    vars_list_text = "Variables disponibles pour les formules (Nom = Donnée de la courbe) : \n"
    for name, (data, unit) in available_data.items():
        vars_list_text += f"  - {name} (Unité: {unit})\n"
    tk.Label(header_frame, text=vars_list_text, justify=tk.LEFT, fg='darkgreen').pack(anchor='w')
    tk.Label(header_frame, text="Utilisez les fonctions mathématiques Python/Numpy (ex: np.sin(t), np.exp(-U/tau), 2*I+3)").pack(anchor='w')
    entry_frame = ttk.Frame(calcul_window)
    entry_frame.pack(fill='x', padx=10, pady=10)
    tk.Label(entry_frame, text="Nom de la nouvelle grandeur:").grid(row=0, column=0, sticky='w', padx=5)
    new_name_var = tk.StringVar(value="Grandeur_Calculee")
    tk.Entry(entry_frame, textvariable=new_name_var, width=30).grid(row=0, column=1, sticky='ew', padx=5)
    tk.Label(entry_frame, text="Unité:").grid(row=1, column=0, sticky='w', padx=5)
    new_unit_var = tk.StringVar(value="U.A.")
    tk.Entry(entry_frame, textvariable=new_unit_var, width=10).grid(row=1, column=1, sticky='w', padx=5)
    tk.Label(entry_frame, text="Formule:").grid(row=2, column=0, sticky='w', padx=5)
    formula_var = tk.StringVar(value="")
    entry_formula = tk.Entry(entry_frame, textvariable=formula_var, width=60)
    entry_formula.grid(row=2, column=1, sticky='ew', padx=5, pady=5)

    def calculate_and_plot():
        name = new_name_var.get().strip()
        unit = new_unit_var.get().strip()
        formula = formula_var.get().strip()
        if not name or not formula:
            messagebox.showwarning("Erreur de calcul", "Veuillez fournir un nom et une formule.")
            return
        eval_env = {'np': np, 't': available_data['t'][0]}
        for var_name, (data, unit_val) in available_data.items():
            if var_name != 't':
                eval_env[var_name] = data
        try:
            if re.search(r'\b(os|sys|file|exec|import|__)\b', formula):
                raise ValueError("Fonctions Python interdites dans la formule pour des raisons de sécurité.")
            result_array = eval(formula, {"__builtins__": None}, eval_env)
            if not isinstance(result_array, np.ndarray) and isinstance(result_array, (int, float)):
                result_array = np.full_like(available_data['t'][0], result_array)
            if not isinstance(result_array, np.ndarray) or len(result_array) != len(available_data['t'][0]):
                raise TypeError("Le résultat n'est pas un tableau de la même taille que les données originales.")
            full_name = f"{name} ({unit})"
            curves_to_plot = [(available_data['t'][0], result_array, full_name, False)]
            open_new_plot_window_tab(curves_to_plot, title_suffix=f"(Calcul : {name})")
            calcul_window.destroy()
        except NameError as e:
            messagebox.showerror("Erreur de Formule", f"Variable ou fonction non définie : {e}. Utilisez 'np.sin()' et les noms des grandeurs disponibles.")
        except TypeError as e:
            messagebox.showerror("Erreur de Calcul", f"Erreur de Type ou de Dimension: {e}. Vérifiez si votre formule est mathématiquement correcte.")
        except Exception as e:
            messagebox.showerror("Erreur Inattendue", f"Une erreur s'est produite lors du calcul: {e}")

    tk.Button(entry_frame, text="Calculer et Afficher sur nouvel Onglet", command=calculate_and_plot, font='Helvetica 10 bold', bg='lightblue').grid(row=3, column=0, columnspan=2, pady=10)
    calcul_window.update_idletasks()
    width = calcul_window.winfo_width()
    height = calcul_window.winfo_height()
    x = (calcul_window.winfo_screenwidth() // 2) - (width // 2)
    y = (calcul_window.winfo_screenheight() // 2) - (height // 2)
    calcul_window.geometry(f'{width}x{height}+{x}+{y}')

# ---------------------------
# Modelling, Derivative, FFT, Measurements
# ---------------------------

def f_lineaire(x, a):
    return a * x

def f_affine(x, a, b):
    return a * x + b

def f_exponentielle(x, A, tau, C):
    return A * np.exp(-x / tau) + C

def f_puissance(x, A, n, B):
    x_safe = np.array([max(1e-9, xi) for xi in x])
    return A * (x_safe ** n) + B

def show_model_results(model_type, params, units, equation):
    dialog = tk.Toplevel()
    dialog.title(f"Résultats Modélisation {model_type}")
    dialog.update_idletasks()
    width = 420
    height = 160 + 28 * len(params)
    x = (dialog.winfo_screenwidth() // 2) - (width // 2)
    y = (dialog.winfo_screenheight() // 2) - (height // 2)
    dialog.geometry(f'{width}x{height}+{x}+{y}')
    tk.Label(dialog, text=f"Modèle : {equation}", font='Helvetica 12 bold', padx=10, pady=10).pack()
    for name, value in params.items():
        unit = units.get(name, 'U.A.')
        tk.Label(dialog,
                 text=f"{name} ({value[1]}) : {value[0]:.4e} {unit}",
                 font='Helvetica 10',
                 justify=tk.LEFT,
                 padx=10).pack(anchor='w')
    tk.Button(dialog, text="OK", command=dialog.destroy).pack(pady=8)

def get_units_for_model(curve_name_with_unit):
    unite_y = "U.A."
    if '(' in curve_name_with_unit and ')' in curve_name_with_unit:
        unite_y = curve_name_with_unit.split('(')[-1].replace(')', '').strip()
    unite_x = 's'
    return unite_y, unite_x

def modeliser_lineaire():
    active_window = get_active_plot_window()
    if not active_window or not active_window['curves_data']:
        messagebox.showwarning("Modélisation", "Aucune courbe pour la modélisation.")
        return
    selected = select_curve_dialog(active_window, title="Sélection de la courbe à modéliser (Linéaire)")
    if selected is None:
        return
    index, t_data, v_data, base_name, _ = selected
    active_curves = active_window['curves_data']
    try:
        popt, pcov = curve_fit(f_lineaire, t_data, v_data, p0=[1.0])
        a = popt[0]
        v_modele = f_lineaire(t_data, a)
        unite_y, unite_x = get_units_for_model(base_name)
        params = {'a': (a, 'Coeff. directeur')}
        units = {'a': f"{unite_y}/{unite_x}"}
        equation = "Y = a * X"
        show_model_results('Linéaire', params, units, equation)
        model_name = f"Modèle Linéaire (y={a:.2e}x) de {base_name}"
        active_curves.append((t_data, v_modele, model_name, False))
        plot_mode_unique(active_window)
        auto_calibrate_plot(active_window)
    except Exception as e:
        messagebox.showerror("Erreur Modélisation Linéaire", f"Erreur lors de la modélisation linéaire: {e}")

def modeliser_affine():
    active_window = get_active_plot_window()
    if not active_window or not active_window['curves_data']:
        messagebox.showwarning("Modélisation", "Aucune courbe pour la modélisation.")
        return
    selected = select_curve_dialog(active_window, title="Sélection de la courbe à modéliser (Affine)")
    if selected is None:
        return
    index, t_data, v_data, base_name, _ = selected
    active_curves = active_window['curves_data']
    try:
        popt, pcov = curve_fit(f_affine, t_data, v_data)
        a, b = popt[0], popt[1]
        v_modele = f_affine(t_data, a, b)
        unite_y, unite_x = get_units_for_model(base_name)
        params = {'a': (a, 'Coeff. directeur'), 'b': (b, "Ordonnée à l'origine")}
        units = {'a': f"{unite_y}/{unite_x}", 'b': unite_y}
        equation = "Y = a * X + b"
        show_model_results('Affine', params, units, equation)
        model_name = f"Modèle Affine (y={a:.2e}x + {b:.2e})"
        active_curves.append((t_data, v_modele, model_name, False))
        plot_mode_unique(active_window)
        auto_calibrate_plot(active_window)
    except Exception as e:
        messagebox.showerror("Erreur Modélisation Affine", f"Erreur: {e}")

def modeliser_exponentielle():
    active_window = get_active_plot_window()
    if not active_window or not active_window['curves_data']:
        messagebox.showwarning("Modélisation", "Aucune courbe pour la modélisation.")
        return
    selected = select_curve_dialog(active_window, title="Sélection de la courbe à modéliser (Exponentielle)")
    if selected is None:
        return
    index, t_data, v_data, base_name, _ = selected
    active_curves = active_window['curves_data']
    try:
        A0 = v_data[0] - v_data[-1]
        C0 = v_data[-1]
        tau0 = t_data[-1] / 3 if t_data[-1] != 0 else 1.0
        p0 = [A0, tau0, C0]
        popt, pcov = curve_fit(f_exponentielle, t_data, v_data, p0=p0, maxfev=5000)
        A, tau, C = popt
        v_modele = f_exponentielle(t_data, A, tau, C)
        unite_y, unite_x = get_units_for_model(base_name)
        params = {'A': (A, 'Amplitude initiale'), 'tau': (tau, 'Constante de temps'), 'C': (C, 'Offset')}
        units = {'A': unite_y, 'tau': unite_x, 'C': unite_y}
        equation = u"Y = A · exp(-X/τ) + C"
        show_model_results('Exponentielle', params, units, equation)
        model_name = f"Modèle Exp. (A={A:.2e}, τ={tau:.2e})"
        active_curves.append((t_data, v_modele, model_name, False))
        plot_mode_unique(active_window)
        auto_calibrate_plot(active_window)
    except RuntimeError:
        messagebox.showerror("Erreur Modélisation Exp.", "Ajustement non optimal: Vérifiez la forme des données.")
    except Exception as e:
        messagebox.showerror("Erreur Modélisation Exp.", f"Erreur: {e}")

def modeliser_puissance():
    active_window = get_active_plot_window()
    if not active_window or not active_window['curves_data']:
        messagebox.showwarning("Modélisation", "Aucune courbe pour la modélisation.")
        return
    selected = select_curve_dialog(active_window, title="Sélection de la courbe à modéliser (Puissance)")
    if selected is None:
        return
    index, t_data, v_data, base_name, _ = selected
    active_curves = active_window['curves_data']
    try:
        if np.any(t_data <= 0):
            t_data_safe = t_data.copy()
            t_data_safe[t_data_safe <= 0] = 1e-6
            t_data = t_data_safe
        p0 = [1.0, 1.0, 0.0]
        popt, pcov = curve_fit(f_puissance, t_data, v_data, p0=p0, maxfev=5000)
        A, n, B = popt
        v_modele = f_puissance(t_data, A, n, B)
        unite_y, unite_x = get_units_for_model(base_name)
        unite_A = f"{unite_y}/({unite_x}^{n:.2f})" if n != 0 else unite_y
        params = {'A': (A, 'Coeff. multiplicateur'), 'n': (n, 'Exposant'), 'B': (B, 'Offset')}
        units = {'A': unite_A, 'n': 'sans unité', 'B': unite_y}
        equation = u"Y = A · X^n + B"
        show_model_results('Puissance', params, units, equation)
        model_name = f"Modèle Puissance (y={A:.2e}x^{n:.2f} + {B:.2e})"
        active_curves.append((t_data, v_modele, model_name, False))
        plot_mode_unique(active_window)
        auto_calibrate_plot(active_window)
    except RuntimeError:
        messagebox.showerror("Erreur Modélisation Pui.", "Ajustement non optimal: Vérifiez la forme des données.")
    except Exception as e:
        messagebox.showerror("Erreur Modélisation Pui.", f"Erreur: {e}")

def calculer_derivee():
    active_window = get_active_plot_window()
    if not active_window or not active_window['curves_data']:
        messagebox.showwarning("Erreur", "Aucune courbe n'a été acquise pour calculer la dérivée dans l'onglet actif.")
        return
    selected = select_curve_dialog(active_window, title="Sélection de la courbe à dériver")
    if selected is None:
        return
    index, temps, tension, base_name, _ = selected
    active_curves = active_window['curves_data']
    if len(temps) < 2:
        messagebox.showwarning("Erreur", "La courbe sélectionnée est trop courte pour calculer une dérivée.")
        return
    derivee = np.diff(tension) / np.diff(temps)
    temps_derivee = (temps[:-1] + temps[1:]) / 2
    unite_y, unite_x = get_units_for_model(base_name)
    grandeur_derivee = f"Dérivée d({base_name.split('(')[0].strip()})/dt ({unite_y}/{unite_x})"
    active_curves.append((temps_derivee, derivee, grandeur_derivee, False))
    messagebox.showinfo("Calcul réussi", f"La dérivée ({grandeur_derivee}) a été calculée et ajoutée au graphique actif.")
    plot_mode_unique(active_window)
    auto_calibrate_plot(active_window)

def _compute_period_from_peaks(t, v):
    if len(t) < 3:
        return None, None, []
    v = np.asarray(v)
    t = np.asarray(t)
    vmin, vmax = np.min(v), np.max(v)
    amplitude = vmax - vmin
    if amplitude == 0:
        return None, None, []
    threshold = vmin + 0.2 * amplitude
    peaks_idx = []
    for i in range(1, len(v) - 1):
        if v[i] > v[i - 1] and v[i] > v[i + 1] and v[i] >= threshold:
            peaks_idx.append(i)
    peak_times = t[peaks_idx] if peaks_idx else np.array([])

    if len(peak_times) < 2:
        mean_v = np.mean(v)
        crossings = []
        for i in range(len(v) - 1):
            if v[i] < mean_v and v[i + 1] >= mean_v:
                dv = v[i + 1] - v[i]
                if dv == 0:
                    tc = t[i]
                else:
                    frac = (mean_v - v[i]) / dv
                    tc = t[i] + frac * (t[i + 1] - t[i])
                crossings.append(tc)
        peak_times = np.array(crossings)

    if len(peak_times) < 2:
        return None, None, []

    diffs = np.diff(peak_times)
    med = np.median(diffs)
    if med <= 0:
        return None, None, peak_times.tolist()
    diffs_good = diffs[diffs < 10 * med]
    if len(diffs_good) == 0:
        return None, None, peak_times.tolist()
    period_mean = float(np.mean(diffs_good))
    period_std = float(np.std(diffs_good))
    return period_mean, period_std, peak_times.tolist()

def measure_on_curve(active_window, curve_index, t0=None, t1=None, show_peaks_on_plot=False):
    try:
        t_arr, v_arr, name, is_raw = active_window['curves_data'][curve_index]
    except Exception as e:
        raise RuntimeError(f"Impossible de récupérer la courbe : {e}")

    if not hasattr(t_arr, '__len__') or len(t_arr) == 0:
        raise RuntimeError("La courbe sélectionnée ne contient pas de données temporelles.")

    t = np.asarray(t_arr)
    v = np.asarray(v_arr)

    if t0 is not None or t1 is not None:
        mask = np.ones_like(t, dtype=bool)
        if t0 is not None:
            mask &= (t >= t0)
        if t1 is not None:
            mask &= (t <= t1)
        if np.sum(mask) < 2:
            raise RuntimeError("La plage temporelle sélectionnée contient trop peu de points.")
        t = t[mask]
        v = v[mask]

    vmin = float(np.min(v))
    vmax = float(np.max(v))

    period_mean, period_std, peak_times = _compute_period_from_peaks(t, v)
    frequency = None
    if period_mean is not None and period_mean > 0:
        frequency = 1.0 / period_mean

    measurements = {
        'curve_name': name,
        'T_mean_s': period_mean,
        'T_std_s': period_std,
        'f_Hz': frequency,
        'v_min': vmin,
        'v_max': vmax,
        'n_peaks': len(peak_times),
        'peak_times': peak_times
    }

    if show_peaks_on_plot and peak_times:
        try:
            ax = active_window['ax']
            peak_vals = np.interp(np.array(peak_times), np.asarray(t_arr), np.asarray(v_arr))
            ax.scatter(peak_times, peak_vals, c='magenta', marker='x', zorder=10)
            active_window['canvas'].draw_idle()
        except Exception:
            pass

    return measurements

def measure_auto_dialog():
    active_window = get_active_plot_window()
    if not active_window or not active_window['curves_data']:
        messagebox.showwarning("Mesures automatiques", "Aucune courbe disponible dans l'onglet actif.")
        return

    selected = select_curve_dialog(active_window, title="Sélection de la courbe pour mesures automatiques")
    if selected is None:
        return
    curve_index, t_arr, v_arr, name, is_raw = selected

    t_min = float(np.min(t_arr)) if len(t_arr) else 0.0
    t_max = float(np.max(t_arr)) if len(t_arr) else 0.0

    dlg = tk.Toplevel(root)
    dlg.title(f"Mesures automatiques - {name}")
    dlg.geometry("460x300")
    dlg.transient(root)

    frm = ttk.Frame(dlg, padding=10)
    frm.pack(fill='both', expand=True)

    tk.Label(frm, text=f"Courbe : {name}", font=('Helvetica', 11, 'bold')).pack(anchor='w', pady=(0,6))

    tw_frame = ttk.LabelFrame(frm, text="Plage temporelle pour l'analyse (laisser vide = totalité)")
    tw_frame.pack(fill='x', pady=6)
    tk.Label(tw_frame, text="T0 (s):").grid(row=0, column=0, sticky='w', padx=4, pady=2)
    t0_var = tk.StringVar(value=f"{t_min:.6g}")
    e_t0 = tk.Entry(tw_frame, textvariable=t0_var, width=18)
    e_t0.grid(row=0, column=1, padx=4, pady=2)
    tk.Label(tw_frame, text="T1 (s):").grid(row=1, column=0, sticky='w', padx=4, pady=2)
    t1_var = tk.StringVar(value=f"{t_max:.6g}")
    e_t1 = tk.Entry(tw_frame, textvariable=t1_var, width=18)
    e_t1.grid(row=1, column=1, padx=4, pady=2)

    res_frame = ttk.Frame(frm)
    res_frame.pack(fill='both', expand=True, pady=(8,0))

    results_text = tk.Text(res_frame, height=8, wrap=tk.WORD)
    results_text.pack(fill='both', expand=True)

    show_peaks_var = tk.BooleanVar(value=False)
    tk.Checkbutton(frm, text="Afficher les pics détectés sur le graphique", variable=show_peaks_var).pack(anchor='w', pady=6)

    def run_measure():
        t0 = None
        t1 = None
        try:
            t0s = t0_var.get().strip()
            t1s = t1_var.get().strip()
            if t0s != '':
                t0 = float(t0s.replace(',', '.'))
            if t1s != '':
                t1 = float(t1s.replace(',', '.'))
        except Exception:
            messagebox.showwarning("Plage temporelle", "Plage temporelle non valide.")
            return
        try:
            meas = measure_on_curve(active_window, curve_index, t0=t0, t1=t1, show_peaks_on_plot=False)
        except Exception as e:
            messagebox.showerror("Mesures automatiques", f"Erreur lors du calcul des mesures : {e}")
            return
        results_text.delete('1.0', tk.END)
        results_text.insert(tk.END, f"Points détectés (pics) : {meas.get('n_peaks', 0)}\n")
        results_text.insert(tk.END, f"Valeur maximale : {meas['v_max']:.6g}\n")
        results_text.insert(tk.END, f"Valeur minimale : {meas['v_min']:.6g}\n")
        T = meas.get('T_mean_s')
        Tstd = meas.get('T_std_s')
        fval = meas.get('f_Hz')
        if T is not None:
            results_text.insert(tk.END, f"Période (moyenne) T = {T:.6g} s    (écart-type {Tstd:.2g} s)\n")
        else:
            results_text.insert(tk.END, "Période (moyenne) T : non déterminée\n")
        if fval is not None:
            results_text.insert(tk.END, f"Fréquence f = {fval:.6g} Hz\n")
        else:
            results_text.insert(tk.END, "Fréquence f : non déterminée\n")

    def apply_and_close():
        t0 = None
        t1 = None
        try:
            t0s = t0_var.get().strip()
            t1s = t1_var.get().strip()
            if t0s != '':
                t0 = float(t0s.replace(',', '.'))
            if t1s != '':
                t1 = float(t1s.replace(',', '.'))
        except Exception:
            t0 = t1 = None
        if show_peaks_var.get():
            try:
                measure_on_curve(active_window, curve_index, t0=t0, t1=t1, show_peaks_on_plot=True)
            except Exception:
                pass
        dlg.destroy()

    btns = ttk.Frame(frm)
    btns.pack(fill='x', pady=6)
    ttk.Button(btns, text="Calculer", command=run_measure).pack(side='left', padx=4)
    ttk.Button(btns, text="Appliquer (Afficher pics si coché)", command=apply_and_close).pack(side='left', padx=4)
    ttk.Button(btns, text="Fermer", command=dlg.destroy).pack(side='right', padx=4)

    dlg.grab_set()
    dlg.focus_force()
    dlg.wait_window()

def compute_fft_for_curve(t, v):
    t = np.asarray(t)
    v = np.asarray(v)
    if len(t) < 2:
        return np.array([]), np.array([])
    dt = np.diff(t)
    if np.any(dt <= 0):
        order = np.argsort(t)
        t = t[order]
        v = v[order]
        dt = np.diff(t)
    fe = 1.0 / np.mean(dt)
    N = len(v)
    v0 = v - np.mean(v)
    window = np.hanning(N)
    vw = v0 * window
    Vf = np.fft.rfft(vw)
    amplitude = (2.0 / np.sum(window)) * np.abs(Vf)
    freqs = np.fft.rfftfreq(N, d=1.0/fe)
    return freqs, amplitude

def fft_dialog():
    active_window = get_active_plot_window()
    if not active_window or not active_window['curves_data']:
        messagebox.showwarning("FFT", "Aucune courbe disponible dans l'onglet actif.")
        return

    selected = select_curve_dialog(active_window, title="Sélection de la courbe pour FFT")
    if selected is None:
        return
    curve_index, t_arr, v_arr, name, is_raw = selected

    t_min = float(np.min(t_arr)) if len(t_arr) else 0.0
    t_max = float(np.max(t_arr)) if len(t_arr) else 0.0

    dlg = tk.Toplevel(root)
    dlg.title(f"Spectre de Fourier - {name}")
    dlg.geometry("420x240")
    dlg.transient(root)

    frm = ttk.Frame(dlg, padding=10)
    frm.pack(fill='both', expand=True)

    tk.Label(frm, text=f"Courbe : {name}", font=('Helvetica', 11, 'bold')).pack(anchor='w', pady=(0,6))

    tw_frame = ttk.Frame(frm)
    tw_frame.pack(fill='x', pady=4)
    tk.Label(tw_frame, text="T0 (s):").grid(row=0, column=0, sticky='w', padx=4, pady=2)
    t0_var = tk.StringVar(value=f"{t_min:.6g}")
    tk.Entry(tw_frame, textvariable=t0_var, width=18).grid(row=0, column=1, padx=4, pady=2)
    tk.Label(tw_frame, text="T1 (s):").grid(row=1, column=0, sticky='w', padx=4, pady=2)
    t1_var = tk.StringVar(value=f"{t_max:.6g}")
    tk.Entry(tw_frame, textvariable=t1_var, width=18).grid(row=1, column=1, padx=4, pady=2)

    result_label = tk.StringVar(value="")
    tk.Label(frm, textvariable=result_label, foreground='blue').pack(anchor='w', pady=6)

    def run_fft_and_show():
        t0 = None
        t1 = None
        try:
            t0s = t0_var.get().strip()
            t1s = t1_var.get().strip()
            if t0s != '':
                t0 = float(t0s.replace(',', '.'))
            if t1s != '':
                t1 = float(t1s.replace(',', '.'))
        except Exception:
            messagebox.showwarning("Plage temporelle", "Plage temporelle non valide.")
            return

        t = np.asarray(t_arr)
        v = np.asarray(v_arr)
        if t0 is not None or t1 is not None:
            mask = np.ones_like(t, dtype=bool)
            if t0 is not None:
                mask &= (t >= t0)
            if t1 is not None:
                mask &= (t <= t1)
            if np.sum(mask) < 2:
                messagebox.showwarning("FFT", "La plage temporelle contient trop peu de points.")
                return
            t = t[mask]
            v = v[mask]

        freqs, amp = compute_fft_for_curve(t, v)
        if freqs.size == 0:
            messagebox.showwarning("FFT", "Impossible de calculer la FFT (données insuffisantes).")
            return

        idx_max = np.argmax(amp)
        peak_freq = freqs[idx_max]
        peak_amp = amp[idx_max]
        result_label.set(f"Pic dominant: f = {peak_freq:.6g} Hz, amplitude = {peak_amp:.6g}")

        spec_name = f"Spectre FFT de {name}"
        open_new_plot_window_tab([(freqs, amp, spec_name, False)], title_suffix="(FFT)")
        dlg.destroy()

    ttk.Button(frm, text="Calculer et Afficher le Spectre", command=run_fft_and_show).pack(side='left', padx=6, pady=8)
    ttk.Button(frm, text="Fermer", command=dlg.destroy).pack(side='right', padx=6, pady=8)

    dlg.grab_set()
    dlg.focus_force()
    dlg.wait_window()

# ---------------------------
# Plot rendering and autoscale
# ---------------------------

def auto_calibrate_plot(window_data=None):
    global CALIBRE_AFFICHE
    if window_data is None:
        window_data = get_active_plot_window()
        if window_data is None:
            return
    curves_data = window_data['curves_data']
    ax = window_data['ax']
    window_data['_previous_x_limits'] = ax.get_xlim()
    window_data['_previous_y_limits'] = ax.get_ylim()
    if not curves_data:
        ax.set_xlim(window_data['_initial_x_limits'])
        ax.set_ylim(window_data['_initial_y_limits'])
        window_data['canvas'].draw_idle()
        return
    all_t = np.concatenate([t for t, v, nom, _ in curves_data if hasattr(t, 'size') and t.size > 0])
    if all_t.size > 0:
        t_min = all_t.min()
        t_max = all_t.max()
        t_range = t_max - t_min
        if t_range > 0:
            margin_x = t_range * 0.05
            x_min = t_min - margin_x
            x_max = t_max + margin_x
            if x_min >= x_max:
                x_min, x_max = t_min - 0.001, t_max + 0.001
        else:
            x_min, x_max = t_min - 0.001, t_max + 0.001
    else:
        x_min, x_max = window_data['_initial_x_limits']
    ax.set_xlim(x_min, x_max)

    visible_flags = window_data.get('visible_flags', [])
    main_vs = []
    for i, (t, v, nom, _) in enumerate(curves_data):
        if visible_flags and i < len(visible_flags) and not visible_flags[i]:
            continue
        unit = _extract_unit_from_name(nom)
        primary_unit = _extract_unit_from_name(curves_data[0][2]) if curves_data else None
        is_secondary = False
        if i != 0 and ((unit and primary_unit and unit != primary_unit) or ('Dérivée' in nom or 'dérivée' in nom or 'derive' in nom.lower())):
            is_secondary = True
        if is_secondary:
            continue
        if hasattr(v, 'size') and v.size > 0:
            main_vs.append(v)
    if main_vs:
        all_v_main = np.concatenate(main_vs)
        v_min = all_v_main.min()
        v_max = all_v_main.max()
        v_range = v_max - v_min
        if v_range > 0:
            margin_y = v_range * 0.10
            y_min = v_min - margin_y
            y_max = v_max + margin_y
        else:
            y_min = v_min - np.abs(v_min) * 0.1 if v_min != 0 else -1
            y_max = v_max + np.abs(v_max) * 0.1 if v_max != 0 else 1
    else:
        y_min, y_max = window_data['_initial_y_limits']
    ax.set_ylim(y_min, y_max)

    secax = window_data.get('secax')
    if secax is not None:
        sec_vs = []
        for i, (t, v, nom, _) in enumerate(curves_data):
            if visible_flags and i < len(visible_flags) and not visible_flags[i]:
                continue
            unit = _extract_unit_from_name(nom)
            primary_unit = _extract_unit_from_name(curves_data[0][2]) if curves_data else None
            if i != 0 and ((unit and primary_unit and unit != primary_unit) or ('Dérivée' in nom or 'dérivée' in nom or 'derive' in nom.lower())):
                if hasattr(v, 'size') and v.size > 0:
                    sec_vs.append(v)
        if sec_vs:
            all_sec = np.concatenate(sec_vs)
            sv_min = all_sec.min()
            sv_max = all_sec.max()
            sv_range = sv_max - sv_min
            if sv_range > 0:
                margin_s = sv_range * 0.10
                secax.set_ylim(sv_min - margin_s, sv_max + margin_s)
            else:
                secax.set_ylim(sv_min - abs(sv_min)*0.1 if sv_min != 0 else -1, sv_max + abs(sv_max)*0.1 if sv_max != 0 else 1)
    window_data['canvas'].draw_idle()

def de_calibrate_plot(window_data=None):
    if window_data is None:
        window_data = get_active_plot_window()
        if window_data is None:
            messagebox.showwarning("Décalibrage", "Aucun panneau graphique actif trouvé.")
            return
    ax = window_data['ax']
    x_min, x_max = window_data['_previous_x_limits']
    y_min, y_max = window_data['_previous_y_limits']
    if (x_min, x_max) == window_data['_initial_x_limits'] and (y_min, y_max) == window_data['_initial_y_limits']:
        if ax.get_xlim() == window_data['_initial_x_limits'] and ax.get_ylim() == window_data['_initial_y_limits']:
            messagebox.showinfo("Décalibrage", "Le graphique est déjà à ses limites initiales.")
            return
        x_min, x_max = window_data['_initial_x_limits']
        y_min, y_max = window_data['_initial_y_limits']
    ax.set_xlim(x_min, x_max)
    ax.set_ylim(y_min, y_max)
    window_data['_previous_x_limits'] = window_data['_initial_x_limits']
    window_data['_previous_y_limits'] = window_data['_initial_y_limits']
    window_data['canvas'].draw_idle()

def update_plot_label(event=None):
    for window in ALL_PLOT_WINDOWS:
        if window.get('ax') and window.get('canvas'):
            if len(window['curves_data']) == 0:
                if grandeur_physique_var:
                    window['ax'].set_ylabel(grandeur_physique_var.get())
                window['canvas'].draw_idle()

def update_plot_style(style=None, window_data=None):
    if style and plot_style_var:
        plot_style_var.set(style)
    if window_data:
        plot_mode_unique(window_data)
    else:
        w = get_active_plot_window()
        if w:
            plot_mode_unique(w)

def plot_mode_unique(window_data=None):
    global CALIBRE_AFFICHE
    if window_data is None:
        window_data = get_active_plot_window()
        if window_data is None:
            return
    ax = window_data['ax']
    canvas = window_data['canvas']
    curves_data = window_data['curves_data']
    reticule = window_data['reticule']

    if window_data.get('secax') is not None:
        try:
            old = window_data['secax']
            window_data['secax'] = None
            old.remove()
        except Exception:
            pass

    _sync_visible_flags(window_data)
    _sync_curve_colors(window_data)
    visible_flags = window_data.get('visible_flags', [])
    curve_colors = window_data.get('curve_colors', [])

    plot_style = plot_style_var.get() if plot_style_var else Config.PLOT_STYLE

    current_x_lim = ax.get_xlim()
    current_y_lim = ax.get_ylim()

    if current_x_lim != window_data['_initial_x_limits'] or current_y_lim != window_data['_initial_y_limits']:
        window_data['_previous_x_limits'] = current_x_lim
        window_data['_previous_y_limits'] = current_y_lim

    ax.clear()

    primary_unit = None
    if curves_data:
        primary_unit = _extract_unit_from_name(curves_data[0][2])

    secondary_indices = set()
    for i, (_, v, nom, _) in enumerate(curves_data):
        if i == 0:
            continue
        unit = _extract_unit_from_name(nom)
        if (unit and primary_unit and unit != primary_unit) or ('Dérivée' in nom or 'dérivée' in nom or 'derive' in nom.lower()):
            secondary_indices.add(i)

    secax = None
    if secondary_indices:
        secax = ax.twinx()
        window_data['secax'] = secax
        sec_color = window_data.get('sec_color', 'tab:red')
        try:
            secax.spines['right'].set_color(sec_color)
            secax.yaxis.label.set_color(sec_color)
            secax.tick_params(axis='y', colors=sec_color)
            secax.yaxis.set_label_position("right")
            secax.yaxis.tick_right()
        except Exception:
            pass
    else:
        window_data['secax'] = None
        sec_color = window_data.get('sec_color', 'tab:red')

    def _curve_on_secondary(idx):
        return idx in secondary_indices

    active_idx = reticule.active_curve_index
    if secax is not None and _curve_on_secondary(active_idx):
        reticule.ax = secax
    else:
        reticule.ax = ax
    reticule.curves_data = curves_data

    target_axis_for_artists = reticule.ax
    try:
        for a in (ax, window_data.get('secax')):
            if a is None:
                continue
            for artist in (reticule.v_line, reticule.h_line, reticule.coord_text):
                try:
                    if artist in a.artists:
                        a.artists.remove(artist)
                except Exception:
                    pass
        if reticule.v_line not in target_axis_for_artists.artists:
            target_axis_for_artists.add_artist(reticule.v_line)
        if reticule.h_line not in target_axis_for_artists.artists:
            target_axis_for_artists.add_artist(reticule.h_line)
        if reticule.coord_text not in target_axis_for_artists.artists:
            target_axis_for_artists.add_artist(reticule.coord_text)
    except Exception:
        pass

    if hasattr(reticule, 'coord_text') and reticule.coord_text is not None:
        reticule.coord_text.set_transform(target_axis_for_artists.transAxes)

    grandeur_nom_y = (grandeur_physique_var.get() if grandeur_physique_var else "Grandeur")
    if curves_data:
        try:
            active_index = reticule.active_curve_index
            if 0 <= active_index < len(curves_data):
                if _curve_on_secondary(active_index) and secax is not None:
                    secax.set_ylabel(curves_data[active_index][2])
                else:
                    ax.set_ylabel(curves_data[active_index][2])
        except Exception:
            grandeur_nom_y = curves_data[0][2]

    ax.set_title(f"Acquisition (Bloc) - Superposition de {len(curves_data)} courbes")
    ax.set_xlabel("Temps (s)")
    if not secax:
        ax.set_ylabel(grandeur_nom_y)
    else:
        ax.set_ylabel(curves_data[0][2] if curves_data else grandeur_nom_y)

    ax.grid(True)

    if curves_data:
        for i, (t, v, nom, is_raw) in enumerate(curves_data):
            if visible_flags and i < len(visible_flags) and not visible_flags[i]:
                continue
            default_color = plt.cm.viridis(i / max(1, len(curves_data)))
            target_ax = secax if (secax is not None and i in secondary_indices) else ax

            # use user color override if present
            if i < len(curve_colors) and curve_colors[i] is not None:
                linecolor = curve_colors[i]
            else:
                if target_ax is secax:
                    linecolor = sec_color
                else:
                    if not is_raw:
                        linecolor = 'red' if 'Modèle' in nom else ('blue' if 'Dérivée' in nom or 'Calcul' in nom else default_color)
                    else:
                        linecolor = default_color

            if not is_raw:
                linestyle = '--'
                target_ax.plot(t, v, label=nom, color=linecolor, linestyle=linestyle, linewidth=2)
            else:
                marker = '+' if plot_style in ["Points", "Points + Courbe"] else ''
                linestyle = '-' if plot_style in ["Courbe seule", "Points + Courbe"] else 'None'
                if len(t) > 0 and len(v) > 0:
                    target_ax.plot(t, v, label=nom, color=linecolor, linestyle=linestyle, marker=marker, markersize=6, linewidth=1)

        handles, labels = ax.get_legend_handles_labels()
        if secax is not None:
            h2, l2 = secax.get_legend_handles_labels()
            handles += h2
            labels += l2
        if handles:
            ax.legend(handles, labels, loc='upper right')

    canvas.draw_idle()

# ---------------------------
# Mode permanent / oscillo, acquisition, exporter, rename/recolor, selection dialogs
# ---------------------------

def plot_mode_permanent():
    messagebox.showwarning("Attention", "Le mode Permanent (Oscilloscope) n'est pas adapté à la gestion par onglets et s'ouvrira dans une fenêtre séparée.")
    global sysam_interface, CALIBRE_AFFICHE
    fig, ax = plt.subplots()
    grandeur_nom = (grandeur_physique_var.get() if grandeur_physique_var else "Grandeur")
    titre = f"Mode Permanent (Oscillo) - EA{Config.VOIE_ACQ} à {Config.FE:.0f} Hz"
    if Config.MODE_DECLENCHEMENT == "Automatique sur seuil":
        titre += f" (Déclenchement Seuil sur EA{Config.VOIE_TRIG})"
    ax.set_title(titre)
    ax.set_xlabel("Temps (s)")
    ax.set_ylabel(grandeur_nom)
    ax.set_ylim(-CALIBRE_AFFICHE * Config.DEFAULT_Y_MARGIN, CALIBRE_AFFICHE * Config.DEFAULT_Y_MARGIN)
    ax.grid(True)
    line, = init_oscillo(ax)
    ani = animation.FuncAnimation(fig, update_oscillo, fargs=(sysam_interface, ax, line), interval=50, blit=True)
    try:
        plt.show()
    finally:
        if sysam_interface:
            try:
                sysam_interface.arreter()
                sysam_interface.fermer()
            except:
                pass

def init_oscillo(ax):
    global temps_oscillo, tension_oscillo, line_oscillo
    temps_oscillo = np.zeros(N_POINTS_OSCILLO)
    tension_oscillo = np.zeros(N_POINTS_OSCILLO)
    line_oscillo, = ax.plot(temps_oscillo, tension_oscillo, color='red')
    return line_oscillo,

def update_oscillo(frame, sys_interface, ax, line):
    global temps_oscillo, tension_oscillo
    if sys_interface is None:
        return line,
    try:
        data = sys_interface.paquet(1)
    except Exception:
        return line,
    temps_paquet = data[0]
    tension_paquet = sys_interface.tension(Config.VOIE_ACQ, data=data)
    if len(temps_paquet) > 0:
        n_nouveaux = len(temps_paquet)
        temps_oscillo = np.roll(temps_oscillo, -n_nouveaux)
        tension_oscillo = np.roll(tension_oscillo, -n_nouveaux)
        temps_oscillo[-n_nouveaux:] = temps_paquet
        tension_oscillo[-n_nouveaux:] = tension_paquet
        line.set_data(temps_oscillo, tension_oscillo)
        if temps_oscillo[-1] > temps_oscillo[0]:
            ax.set_xlim(temps_oscillo[0], temps_oscillo[-1])
    return line,

def start_acquisition_and_plot(event=None):
    global sysam_interface, CALIBRE_AFFICHE, root
    active_window = get_active_plot_window()
    if active_window is None:
        messagebox.showerror("Erreur", "Impossible de déterminer la fenêtre graphique active.")
        return
    active_curves = active_window['curves_data']

    root.withdraw()
    if sysam_interface is not None:
        try:
            sysam_interface.fermer()
        except:
            pass
        sysam_interface = None
    try:
        Config.DUREE = float(duree_var.get())
        Config.CALIBRE = float(calibre_var.get())
        Config.N_POINTS = int(nb_points_var.get())
        Config.VOIE_ACQ = int(voie_acq_var.get().replace("EA", ""))
        Config.MODE_DECLENCHEMENT = mode_declenchement_var.get()
        mode_acq_full = mode_acquisition_var.get()
        if "Permanent" in mode_acq_full:
            Config.MODE_ACQUISITION = "Permanent"
        else:
            Config.MODE_ACQUISITION = "Normal"
        grandeur_nom_defaut = (grandeur_physique_var.get() if grandeur_physique_var else "Grandeur")
        if Config.N_POINTS <= 0 or Config.DUREE <= 0:
            raise ValueError("Durée et Nombre de points doivent être positifs.")
        Config.FE = Config.N_POINTS / Config.DUREE
        fe_display_var.set(f"{Config.FE:.2f}")
        Te_us = (Config.DUREE / Config.N_POINTS) * 1e6
        CALIBRE_AFFICHE = Config.CALIBRE
        sysam_interface = pycan.Sysam("SP5")
        sysam_interface.config_entrees([Config.VOIE_ACQ], [CALIBRE_AFFICHE])
        if Config.MODE_DECLENCHEMENT == "Automatique sur seuil":
            Config.VOIE_TRIG = int(voie_trig_var.get().replace("EA", ""))
            Config.SEUIL = float(seuil_var.get())
            Config.PENTE = pente_var.get()
            pente_val = 1 if Config.PENTE == "Montante" else -1
            Config.PRE_TRIG = int(pre_trig_var.get())
            sysam_interface.config_declenchement(Config.VOIE_TRIG, Config.SEUIL, pente_val, Config.PRE_TRIG)
        if Config.MODE_ACQUISITION == "Normal":
            if not superposition_var.get():
                active_curves.clear()
            sysam_interface.config_echantillon(Te_us, Config.N_POINTS)
            sysam_interface.acquerir()
            sysam_interface.attendre_fin_acquisition()
            temps_data = sysam_interface.temps()
            tension_data = sysam_interface.tension(Config.VOIE_ACQ)
            curve_name = f"{grandeur_nom_defaut} (EA{Config.VOIE_ACQ})"
            is_raw_data = True
            active_curves.append((temps_data, tension_data, curve_name, is_raw_data))
            sysam_interface.fermer()
            sysam_interface = None
            if len(active_curves) == 1:
                active_window['ax'].set_ylabel(curve_name)
            root.deiconify()
            plot_mode_unique(active_window)
            auto_calibrate_plot(active_window)
        elif Config.MODE_ACQUISITION == "Permanent":
            Te_us_oscillo = (1.0 / Config.FE) * 1e6
            sysam_interface.config_echantillon_permanent(Te_us_oscillo, -1)
            sysam_interface.acquerir()
            root.deiconify()
            plot_mode_permanent()
    except ValueError as e:
        root.deiconify()
        messagebox.showerror("Erreur de Paramètre", str(e))
    except Exception as e:
        root.deiconify()
        messagebox.showerror("Erreur Pycanum/Matériel", f"Erreur : {e}")
        if sysam_interface:
            try:
                sysam_interface.fermer()
            except:
                pass
            sysam_interface = None

def exporter_csv():
    active_window = get_active_plot_window()
    if not active_window or not active_window['curves_data']:
        messagebox.showwarning("Exportation", "Aucune donnée acquise dans l'onglet actif à exporter.")
        return
    ALL_CURVES_ACTIVE = active_window['curves_data']
    try:
        filepath = filedialog.asksaveasfilename(defaultextension=".csv",
                                                filetypes=[("Fichiers CSV", "*.csv")],
                                                title="Exporter les données des courbes de l'onglet actif")
        if not filepath:
            return
        max_len = max(len(t) for t, v, nom, _ in ALL_CURVES_ACTIVE)
        with open(filepath, 'w', newline='', encoding='utf-8') as f:
            writer = csv.writer(f, delimiter=';')
            headers = []
            for t, v, nom, _ in ALL_CURVES_ACTIVE:
                headers.extend([f'Temps (s) [{nom}]', f'Grandeur [{nom}]'])
            writer.writerow(headers)
            for i in range(max_len):
                row = []
                for t, v, nom, _ in ALL_CURVES_ACTIVE:
                    t_val = f"{t[i]:.6f}".replace('.', ',') if i < len(t) else ""
                    v_val = f"{v[i]:.6f}".replace('.', ',') if i < len(v) else ""
                    row.append(t_val)
                    row.append(v_val)
                writer.writerow(row)
        messagebox.showinfo("Exportation", f"Données exportées avec succès dans: {os.path.basename(filepath)}")
    except Exception as e:
        messagebox.showerror("Erreur d'exportation", f"Impossible d'exporter les données: {e}")

def menu_imprimer():
    """
    Ouvre un dialogue permettant de :
     - choisir l'imprimante (liste construite depuis le système),
     - ouvrir les paramètres/propriétés de l'imprimante sélectionnée,
     - imprimer toutes les courbes visibles de l'onglet graphique actif.
    Le dialogue fournit des options multi-plateforme 'best-effort'.
    """
    try:
        active_window = get_active_plot_window()
        if not active_window or not active_window.get('curves_data'):
            messagebox.showwarning("Imprimer", "Aucune courbe disponible à imprimer.")
            return

        # Collect visible curves from active window
        _sync_visible_flags(active_window)
        curves = active_window['curves_data']
        visible_flags = active_window.get('visible_flags', [True] * len(curves))
        visible_curves = [(t, v, name) for (t, v, name, _), vis in zip(curves, visible_flags) if vis]

        if not visible_curves:
            messagebox.showwarning("Imprimer", "Aucune courbe visible à l'impression.")
            return

        # Get system printers
        printers = _get_system_printers()
        default_printer = printers[0] if printers else None

        # Build a dialog to choose printer and optionally open settings
        dlg = tk.Toplevel(root)
        dlg.title("Imprimer - Choix imprimante et paramètres")
        dlg.geometry("560x220")
        dlg.transient(root)

        frm = ttk.Frame(dlg, padding=10)
        frm.pack(fill='both', expand=True)

        tk.Label(frm, text="Imprimante :", font=('Helvetica', 10, 'bold')).grid(row=0, column=0, sticky='w', padx=4, pady=6)
        printer_var = tk.StringVar(value=default_printer or "")
        printer_combo = ttk.Combobox(frm, values=printers if printers else ['(Aucune imprimante détectée)'], textvariable=printer_var, state='readonly' if printers else 'disabled', width=50)
        printer_combo.grid(row=0, column=1, sticky='w', padx=4, pady=6)

        def on_refresh_printers():
            p_list = _get_system_printers()
            if not p_list:
                messagebox.showwarning("Imprimantes", "Aucune imprimante détectée sur le système.")
                printer_combo.config(values=['(Aucune imprimante détectée)'], state='disabled')
                printer_var.set('')
            else:
                printer_combo.config(values=p_list, state='readonly')
                printer_var.set(p_list[0])

        ttk.Button(frm, text="Rafraîchir la liste", command=on_refresh_printers).grid(row=0, column=2, sticky='w', padx=6)

        tk.Label(frm, text="Options :", font=('Helvetica', 10, 'bold')).grid(row=1, column=0, sticky='nw', padx=4, pady=6)
        options_frame = ttk.Frame(frm)
        options_frame.grid(row=1, column=1, columnspan=2, sticky='w', padx=4)
        copies_var = tk.IntVar(value=1)
        tk.Label(options_frame, text="Exemplaires :").grid(row=0, column=0, sticky='w')
        tk.Spinbox(options_frame, from_=1, to=99, width=5, textvariable=copies_var).grid(row=0, column=1, sticky='w', padx=6)

        scale_var = tk.DoubleVar(value=100.0)
        tk.Label(options_frame, text="Échelle (%):").grid(row=0, column=2, sticky='w', padx=(12,0))
        tk.Spinbox(options_frame, from_=10, to=500, increment=10, width=6, textvariable=scale_var).grid(row=0, column=3, sticky='w', padx=6)

        def open_settings():
            pname = printer_var.get()
            if not pname:
                messagebox.showwarning("Paramètres", "Aucune imprimante sélectionnée.")
                return
            ok = _open_printer_settings(pname)
            if not ok:
                messagebox.showinfo("Paramètres", "Impossible d'ouvrir une boîte de dialogue de paramètres pour cette imprimante sur ce système.")

        ttk.Button(frm, text="Paramètres de l'imprimante...", command=open_settings).grid(row=2, column=1, sticky='w', padx=4, pady=(8,0))

        def do_print():
            pname = printer_var.get() if printer_var.get() else None
            # Render the visible curves into a temporary image (all curves on one figure)
            fig, ax = plt.subplots(figsize=(11, 8.5), dpi=150)  # landscape-ish A4
            for t, v, name in visible_curves:
                try:
                    ax.plot(t, v, label=name)
                except Exception:
                    pass
            ax.set_title("Impression - Affichage courant")
            ax.set_xlabel("Temps (s)")
            ax.set_ylabel(grandeur_physique_var.get() if grandeur_physique_var else "Grandeur")
            ax.grid(True)
            ax.legend(loc='upper right', fontsize='small')

            tmp_fd, tmp_path = tempfile.mkstemp(suffix='.png')
            os.close(tmp_fd)
            try:
                fig.savefig(tmp_path, bbox_inches='tight')
            finally:
                plt.close(fig)

            dispatched = _print_file_to_printer(tmp_path, printer_name=pname)
            if dispatched:
                messagebox.showinfo("Imprimer", "La tâche d'impression a été envoyée au système (commande envoyée).")
                dlg.destroy()
            else:
                resp = messagebox.askyesno("Imprimer", f"Impossible d'envoyer le fichier directement à l'imprimante.\nLe fichier PNG a été créé :\n{tmp_path}\n\nVoulez-vous ouvrir le dossier contenant le fichier pour imprimer manuellement ?")
                if resp:
                    try:
                        folder = os.path.dirname(tmp_path)
                        if platform.system() == 'Windows':
                            os.startfile(folder)
                        elif platform.system() == 'Darwin':
                            subprocess.run(['open', folder])
                        else:
                            subprocess.run(['xdg-open', folder])
                    except Exception:
                        messagebox.showinfo("Imprimer", f"Ouvrez manuellement : {tmp_path}")

        btns = ttk.Frame(frm)
        btns.grid(row=4, column=0, columnspan=3, pady=12)
        ttk.Button(btns, text="Imprimer", command=do_print).pack(side='left', padx=6)
        ttk.Button(btns, text="Annuler", command=dlg.destroy).pack(side='right', padx=6)

        dlg.grab_set()
        dlg.focus_force()
        dlg.wait_window()

    except Exception as e:
        messagebox.showerror("Imprimer", f"Erreur lors de l'impression : {e}")

# ---------------------------
# Rename / recolor / select curve / copy to clipboard
# ---------------------------

def rename_curve_dialog():
    active_window = get_active_plot_window()
    if not active_window or not active_window['curves_data']:
        messagebox.showwarning("Renommer la courbe", "Aucune courbe disponible.")
        return
    selected = select_curve_dialog(active_window, title="Sélectionnez la courbe à renommer")
    if selected is None:
        return
    idx, t, v, name, is_raw = selected
    new_name = simpledialog.askstring("Renommer", f"Nom actuel : {name}\nNouveau nom :")
    if new_name and new_name.strip():
        active_window['curves_data'][idx] = (t, v, new_name.strip(), is_raw)
        plot_mode_unique(active_window)

def recolor_curve_dialog():
    active_window = get_active_plot_window()
    if not active_window or not active_window['curves_data']:
        messagebox.showwarning("Recolorer la courbe", "Aucune courbe disponible.")
        return
    selected = select_curve_dialog(active_window, title="Sélectionnez la courbe à recolorer")
    if selected is None:
        return
    idx, _, _, name, _ = selected
    color = colorchooser.askcolor(title=f"Choisir couleur pour {name}")
    if color and color[1]:
        _sync_curve_colors(active_window)
        active_window['curve_colors'][idx] = color[1]
        plot_mode_unique(active_window)

def select_curve_dialog(active_window, title="Sélection de la courbe"):
    curves_list = active_window['curves_data']
    if not curves_list:
        messagebox.showwarning("Erreur", "Aucune courbe n'est présente dans l'onglet actif.")
        return None
    if len(curves_list) == 1:
        t, v, name, is_raw = curves_list[0]
        return (0, t, v, name, is_raw)
    selection_window = tk.Toplevel(root)
    selection_window.title(title)
    tk.Label(selection_window, text="Sélectionnez la courbe à utiliser:", font='Helvetica 10 bold', padx=10, pady=10).pack()
    listbox = tk.Listbox(selection_window, width=60, height=min(20, len(curves_list)))
    for i, (_, _, name, is_raw) in enumerate(curves_list):
        data_type = "(Acquisition/Importation)" if is_raw else "(Calcul/Modèle)"
        listbox.insert(tk.END, f"[{i+1}] {name} {data_type}")
    listbox.pack(padx=10, pady=5)
    result = []
    def on_select():
        try:
            index = listbox.curselection()[0]
            t, v, name, is_raw = curves_list[index]
            result.extend([index, t, v, name, is_raw])
            selection_window.destroy()
        except IndexError:
            messagebox.showwarning("Sélection", "Veuillez sélectionner une courbe.")
    tk.Button(selection_window, text="Confirmer la sélection", command=on_select, pady=5).pack(pady=10)
    listbox.bind('<Double-1>', lambda event: on_select())
    root.wait_window(selection_window)
    return tuple(result) if result else None

def menu_copier():
    """
    Copie les données de la courbe active dans le presse-papiers sous forme CSV (semicolon-separated).
    Format : Temps (s);Valeur
    """
    try:
        active_window = get_active_plot_window()
        if not active_window or not active_window.get('curves_data'):
            messagebox.showwarning("Copier", "Aucune courbe disponible à copier.")
            return
        idx = 0
        try:
            idx = active_window['reticule'].active_curve_index
        except Exception:
            idx = 0
        curves = active_window['curves_data']
        if idx < 0 or idx >= len(curves):
            idx = 0
        t_arr, v_arr, name, is_raw = curves[idx]
        lines = []
        lines.append(f"# Courbe: {name}")
        lines.append("Temps (s);Valeur")
        t_list = np.asarray(t_arr).tolist()
        v_list = np.asarray(v_arr).tolist()
        n = max(len(t_list), len(v_list))
        for i in range(n):
            tval = "" if i >= len(t_list) else f"{t_list[i]:.12g}"
            vval = "" if i >= len(v_list) else f"{v_list[i]:.12g}"
            lines.append(f"{tval};{vval}")
        csv_text = "\n".join(lines)
        root.clipboard_clear()
        root.clipboard_append(csv_text)
        root.update()
        messagebox.showinfo("Copier", f"Les données de la courbe '{name}' ont été copiées dans le presse-papiers.")
    except Exception as e:
        messagebox.showerror("Copier", f"Impossible de copier les données: {e}")

# ---------------------------
# Main window & menus
# ---------------------------

def update_fe_and_xaxis(event=None):
    global ALL_PLOT_WINDOWS
    try:
        duree = float(duree_var.get())
        n_points = int(nb_points_var.get())
        if duree <= 0 or n_points <= 0:
            raise ValueError("Durée et Nombre de points doivent être positifs.")
        Config.DUREE = duree
        Config.N_POINTS = n_points
        fe = n_points / duree
        fe_display_var.set(f"{fe:.2f}")
        for window in ALL_PLOT_WINDOWS:
            if window.get('ax') and window.get('canvas'):
                current_y_lim = window['ax'].get_ylim()
                window['ax'].set_xlim(0, duree)
                window['ax'].set_ylim(current_y_lim)
                window['_initial_x_limits'] = (0, duree)
                window['_previous_x_limits'] = (0, duree)
                window['canvas'].draw_idle()
    except ValueError:
        pass

def update_trigger_fields(*args):
    mode = mode_declenchement_var.get()
    if mode == "Manuel":
        state = tk.DISABLED
        fg_color = 'grey50'
    else:
        state = tk.NORMAL
        fg_color = 'black'
    widgets_to_disable = [menu_voie_trig, entry_seuil, menu_pente, entry_pre_trig]
    labels_to_color = [label_voie_trig, label_seuil, label_pente, label_pre_trig]
    for widget in widgets_to_disable:
        try:
            widget.config(state=state)
        except Exception:
            pass
    for label in labels_to_color:
        try:
            label.config(fg=fg_color)
        except Exception:
            pass

def reset_acquisition_params():
    Config.FE = 5000.0
    Config.DUREE = 0.02
    Config.CALIBRE = 10.0
    Config.N_POINTS = 100
    Config.VOIE_ACQ = 0
    Config.MODE_ACQUISITION = "Normal"
    Config.MODE_DECLENCHEMENT = "Manuel"
    Config.VOIE_TRIG = 0
    Config.SEUIL = 0.0
    Config.PENTE = "Montante"
    Config.PRE_TRIG = 0
    duree_var.set(str(Config.DUREE))
    nb_points_var.set(str(Config.N_POINTS))
    calibre_var.set(str(Config.CALIBRE))
    voie_acq_var.set(f"EA{Config.VOIE_ACQ}")
    mode_declenchement_var.set(Config.MODE_DECLENCHEMENT)
    mode_acquisition_var.set("Normal")
    superposition_var.set(False)
    fe_display_var.set(f"{Config.N_POINTS/Config.DUREE:.2f}")
    if grandeur_physique_var:
        grandeur_physique_var.set("Tension (V)")
    voie_trig_var.set(f"EA{Config.VOIE_TRIG}")
    seuil_var.set(str(Config.SEUIL))
    pente_var.set(Config.PENTE)
    pre_trig_var.set(str(Config.PRE_TRIG))
    update_fe_and_xaxis()
    update_trigger_fields()

def menu_nouveau():
    global ALL_PLOT_WINDOWS
    reset_acquisition_params()
    new_window = open_new_plot_window_tab()
    new_window['curves_data'].clear()
    plot_mode_unique(new_window)
    messagebox.showinfo("Nouveau", "Paramètres d'acquisition réinitialisés et nouvel onglet graphique créé.")

def menu_ouvrir():
    global duree_var, superposition_var, CALIBRE_AFFICHE
    active_window = get_active_plot_window()
    if not active_window:
        messagebox.showwarning("Erreur", "Aucun panneau graphique actif trouvé.")
        return
    active_curves = active_window['curves_data']
    try:
        filepath = filedialog.askopenfilename(filetypes=[("Fichiers CSV", "*.csv")], title="Ouvrir un fichier de données")
        if not filepath:
            return
        temps_list = []
        tension_list = []
        curve_name = "Importé"
        is_raw_data = True
        with open(filepath, 'r', newline='', encoding='utf-8') as f:
            reader = csv.reader(f, delimiter=';')
            headers = next(reader)
            if len(headers) >= 2:
                try:
                    full_name = headers[1].split('[')[-1].replace(']', '').strip()
                    curve_name = full_name
                    if not active_curves and grandeur_physique_var:
                        grandeur_physique_var.set(curve_name)
                except Exception:
                    curve_name = "Données Importées (V)"
            for i, row in enumerate(reader):
                if len(row) >= 2:
                    try:
                        t = float(row[0].replace(',', '.'))
                        v = float(row[1].replace(',', '.'))
                        temps_list.append(t)
                        tension_list.append(v)
                    except ValueError:
                        continue
        if not temps_list:
            messagebox.showwarning("Erreur", "Le fichier CSV ne contient aucune donnée valide.")
            return
        temps_data = np.array(temps_list)
        tension_data = np.array(tension_list)
        if not superposition_var.get():
            active_curves.clear()
        curve_display_name = curve_name
        active_curves.append((temps_data, tension_data, curve_display_name, is_raw_data))
        if len(temps_data) > 0:
            Config.DUREE = float(np.max(temps_data))
            duree_var.set(f"{Config.DUREE:.3f}")
            update_fe_and_xaxis()
        new_calibre = np.ceil(np.max(np.abs(tension_data)) * 1.1) if tension_data.size > 0 else Config.CALIBRE
        if new_calibre == 0:
            new_calibre = 10.0
        CALIBRE_AFFICHE = new_calibre
        if len(active_curves) == 1 or not superposition_var.get():
            active_window['ax'].set_ylabel(curve_display_name)
        plot_mode_unique(active_window)
        auto_calibrate_plot(active_window)
        messagebox.showinfo("Ouverture réussie", f"Données '{curve_display_name}' chargées avec {len(temps_data)} points dans l'onglet actif.")
    except Exception as e:
        messagebox.showerror("Erreur d'Ouverture", f"Impossible d'ouvrir ou de lire le fichier: {e}")

def setup_main_window():
    global root, grandeur_physique_var, duree_var, superposition_var
    global nb_points_var, calibre_var, voie_acq_var, mode_declenchement_var
    global mode_acquisition_var, fe_display_var
    global voie_trig_var, seuil_var, pente_var, pre_trig_var
    global menu_voie_trig, entry_seuil, menu_pente, entry_pre_trig
    global label_voie_trig, label_seuil, label_pente, label_pre_trig
    global plot_style_var

    root = tk.Tk()
    root.title("Acquisition Sysam SP5 - Alternative LatisPro (v17)")
    root.protocol("WM_DELETE_WINDOW", close_program)
    # bind F10 using a lambda so the name start_acquisition_and_plot is resolved at event time
    root.bind('<F10>', lambda event: start_acquisition_and_plot(event))

    duree_var = tk.StringVar(value=str(Config.DUREE))
    nb_points_var = tk.StringVar(value=str(Config.N_POINTS))
    calibre_var = tk.StringVar(value=str(Config.CALIBRE))
    voie_acq_var = tk.StringVar(value=f"EA{Config.VOIE_ACQ}")
    mode_declenchement_var = tk.StringVar(value=Config.MODE_DECLENCHEMENT)
    mode_acquisition_var = tk.StringVar(value="Normal")
    superposition_var = tk.BooleanVar(value=False)
    fe_display_var = tk.StringVar(value=f"{Config.N_POINTS/Config.DUREE:.2f}")
    grandeur_physique_var = tk.StringVar(value="Tension (V)")
    voie_trig_var = tk.StringVar(value=f"EA{Config.VOIE_TRIG}")
    seuil_var = tk.StringVar(value=str(Config.SEUIL))
    pente_var = tk.StringVar(value=Config.PENTE)
    pre_trig_var = tk.StringVar(value=str(Config.PRE_TRIG))
    plot_style_var = tk.StringVar(value=Config.PLOT_STYLE)

    # Menu bar
    menubar = tk.Menu(root)
    root.config(menu=menubar)

    # Fichier
    file_menu = tk.Menu(menubar, tearoff=0)
    menubar.add_cascade(label="Fichier", menu=file_menu)
    file_menu.add_command(label="Nouveau", command=menu_nouveau)
    file_menu.add_command(label="Ouvrir...", command=menu_ouvrir)
    file_menu.add_command(label="Enregistrer...", command=lambda: messagebox.showinfo("Enregistrer", "Non implémenté"))
    file_menu.add_command(label="Exporter (CSV)...", command=exporter_csv)
    file_menu.add_separator()
    file_menu.add_command(label="Imprimer la courbe...", command=menu_imprimer)
    file_menu.add_separator()
    file_menu.add_command(label="Quitter", command=close_program)

    # Edition
    edit_menu = tk.Menu(menubar, tearoff=0)
    menubar.add_cascade(label="Édition", menu=edit_menu)
    edit_menu.add_command(label="Copier", command=menu_copier)

    # Outils
    tools_menu = tk.Menu(menubar, tearoff=0)
    menubar.add_cascade(label="Outils", menu=tools_menu)
    tools_menu.add_command(label="Nouvelle fenêtre graphique (Onglet)", command=open_new_plot_window_tab)
    tools_menu.add_command(label="Tableau des valeurs expérimentales", command=open_data_table)
    tools_menu.add_command(label="Feuille de calcul (Nouvelles Grandeurs)", command=open_calcul_sheet)
    tools_menu.add_separator()
    tools_menu.add_command(label="Calculer dérivée (dY/dt)", command=calculer_derivee)
    tools_menu.add_command(label="Mesures automatiques (T, f, Vmax, Vmin)", command=measure_auto_dialog)
    tools_menu.add_command(label="Spectre de Fourier (FFT)", command=fft_dialog)
    tools_menu.add_command(label="Gérer les courbes...", command=lambda: manage_curves_dialog(get_active_plot_window()))

    # Modélisation submenu
    model_menu = tk.Menu(tools_menu, tearoff=0)
    tools_menu.add_cascade(label="Modélisation", menu=model_menu)
    model_menu.add_command(label="Linéaire (y = ax)", command=modeliser_lineaire)
    model_menu.add_command(label="Affine (y = ax + b)", command=modeliser_affine)
    model_menu.add_command(label="Exponentielle (y = A·exp(-t/τ) + C)", command=modeliser_exponentielle)
    model_menu.add_command(label="Puissance (y = A·tⁿ + B)", command=modeliser_puissance)

    # Options menu
    options_menu = tk.Menu(menubar, tearoff=0)
    menubar.add_cascade(label="Options", menu=options_menu)
    options_menu.add_command(label="Calibrage Auto (Optimiser l'Affichage)", command=lambda: auto_calibrate_plot())
    options_menu.add_command(label="Décalibrer (Retour affichage initial)", command=lambda: de_calibrate_plot())
    options_menu.add_separator()
    options_menu.add_command(label="Renommer la courbe...", command=rename_curve_dialog)
    options_menu.add_command(label="Recolorer la courbe...", command=recolor_curve_dialog)
    options_menu.add_separator()
    display_style_menu = tk.Menu(options_menu, tearoff=0)
    options_menu.add_cascade(label="Style d'Affichage", menu=display_style_menu)
    style_options = ["Points", "Courbe seule", "Points + Courbe"]
    for style in style_options:
        display_style_menu.add_radiobutton(label=style, command=lambda s=style: update_plot_style(style=s))

    # Help
    help_menu = tk.Menu(menubar, tearoff=0)
    menubar.add_cascade(label="Aide", menu=help_menu)
    help_menu.add_command(label="Fichier d'aide (Fonctionnalités)", command=lambda: messagebox.showinfo("Aide", "Voir la documentation intégrée."))
    help_menu.add_separator()
    help_menu.add_command(label="À propos", command=lambda: messagebox.showinfo("À propos", "Sysam SP5 Acquisition - LatisLibre"))

    # Main UI layout: controls (left) + plot notebook (right)
    main_frame = tk.Frame(root)
    main_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

    control_frame = tk.Frame(main_frame, padx=15, pady=15, bd=2, relief=tk.GROOVE)
    control_frame.pack(side=tk.LEFT, fill=tk.Y, padx=10, pady=10)

    row_idx = 0
    ttk.Separator(control_frame, orient=tk.HORIZONTAL).grid(row=row_idx, column=0, columnspan=2, sticky='ew', pady=5)
    row_idx += 1
    tk.Label(control_frame, text="MODE D'ACQUISITION", font='Helvetica 10 bold', fg='darkblue').grid(row=row_idx, column=0, columnspan=2, sticky="w", pady=5)
    row_idx += 1

    tk.Label(control_frame, text="Mode :").grid(row=row_idx, column=0, sticky="w")
    mode_acq_options = ["Normal", "Permanent (mode oscilloscope)"]
    tk.OptionMenu(control_frame, mode_acquisition_var, *mode_acq_options).grid(row=row_idx, column=1, padx=5, pady=5)
    row_idx += 1

    tk.Checkbutton(control_frame, text="Superposer les courbes", variable=superposition_var).grid(row=row_idx, column=0, columnspan=2, sticky="w", pady=5)
    row_idx += 1

    ttk.Separator(control_frame, orient=tk.HORIZONTAL).grid(row=row_idx, column=0, columnspan=2, sticky='ew', pady=5)
    row_idx += 1

    tk.Label(control_frame, text="ÉCHANTILLONNAGE / CALIBRE", font='Helvetica 10 bold', fg='darkblue').grid(row=row_idx, column=0, columnspan=2, sticky="w", pady=5)
    row_idx += 1

    tk.Label(control_frame, text="Voie d'Acquisition:").grid(row=row_idx, column=0, sticky="w")
    voie_options = [f"EA{i}" for i in range(8)]
    tk.OptionMenu(control_frame, voie_acq_var, *voie_options).grid(row=row_idx, column=1, padx=5, pady=5)
    row_idx += 1

    tk.Label(control_frame, text="Calibre (V):").grid(row=row_idx, column=0, sticky="w")
    calibre_options = ["10.0", "5.0", "2.0", "1.0"]
    tk.OptionMenu(control_frame, calibre_var, *calibre_options).grid(row=row_idx, column=1, padx=5, pady=5)
    row_idx += 1

    tk.Label(control_frame, text="Durée Totale Δt (s):").grid(row=row_idx, column=0, sticky="w")
    entry_duree = tk.Entry(control_frame, textvariable=duree_var)
    entry_duree.grid(row=row_idx, column=1, padx=5, pady=5)
    entry_duree.bind('<Return>', update_fe_and_xaxis)
    row_idx += 1

    tk.Label(control_frame, text="Nombre de Points (N):").grid(row=row_idx, column=0, sticky="w")
    entry_n_points = tk.Entry(control_frame, textvariable=nb_points_var)
    entry_n_points.grid(row=row_idx, column=1, padx=5, pady=5)
    entry_n_points.bind('<Return>', update_fe_and_xaxis)
    row_idx += 1

    tk.Label(control_frame, text="Fréquence d'échantillonnage Fe (Hz):").grid(row=row_idx, column=0, sticky="w")
    tk.Label(control_frame, textvariable=fe_display_var, fg='black', font='Helvetica 10').grid(row=row_idx, column=1, sticky="w")
    row_idx += 1

    tk.Label(control_frame, text="Fe = N / Δt (calculée automatiquement)", font='Helvetica 8 italic').grid(row=row_idx, column=0, columnspan=2, sticky="w")
    row_idx += 1

    tk.Label(control_frame, text="Grandeur (Nom et Unité):", font='Helvetica 10 bold').grid(row=row_idx, column=0, sticky="w", pady=5)
    entry_grandeur = tk.Entry(control_frame, textvariable=grandeur_physique_var, width=20)
    entry_grandeur.grid(row=row_idx, column=1, padx=5, pady=5)
    entry_grandeur.bind('<Return>', update_plot_label)
    row_idx += 1

    ttk.Separator(control_frame, orient=tk.HORIZONTAL).grid(row=row_idx, column=0, columnspan=2, sticky='ew', pady=5)
    row_idx += 1

    tk.Label(control_frame, text="DÉCLENCHEMENT", font='Helvetica 10 bold', fg='darkblue').grid(row=row_idx, column=0, columnspan=2, sticky="w", pady=5)
    row_idx += 1

    tk.Label(control_frame, text="Mode:").grid(row=row_idx, column=0, sticky="w")
    mode_declenchement_options = ["Manuel", "Automatique sur seuil"]
    mode_declenchement_menu = tk.OptionMenu(control_frame, mode_declenchement_var, *mode_declenchement_options)
    mode_declenchement_menu.grid(row=row_idx, column=1, padx=5, pady=5)
    mode_declenchement_var.trace_add("write", update_trigger_fields)
    row_idx += 1

    label_voie_trig = tk.Label(control_frame, text="Voie de Déclenchement:")
    label_voie_trig.grid(row=row_idx, column=0, sticky="w")
    menu_voie_trig = tk.OptionMenu(control_frame, voie_trig_var, *voie_options)
    menu_voie_trig.grid(row=row_idx, column=1, padx=5, pady=5)
    row_idx += 1

    label_seuil = tk.Label(control_frame, text="Seuil (V):")
    label_seuil.grid(row=row_idx, column=0, sticky="w")
    entry_seuil = tk.Entry(control_frame, textvariable=seuil_var)
    entry_seuil.grid(row=row_idx, column=1, padx=5, pady=5)
    row_idx += 1

    label_pente = tk.Label(control_frame, text="Pente:")
    label_pente.grid(row=row_idx, column=0, sticky="w")
    pente_options = ["Montante", "Descendante"]
    menu_pente = tk.OptionMenu(control_frame, pente_var, *pente_options)
    menu_pente.grid(row=row_idx, column=1, padx=5, pady=5)
    row_idx += 1

    label_pre_trig = tk.Label(control_frame, text="Pré-trig (%):")
    label_pre_trig.grid(row=row_idx, column=0, sticky="w")
    entry_pre_trig = tk.Entry(control_frame, textvariable=pre_trig_var)
    entry_pre_trig.grid(row=row_idx, column=1, padx=5, pady=5)
    row_idx += 1

    ttk.Separator(control_frame, orient=tk.HORIZONTAL).grid(row=row_idx, column=0, columnspan=2, sticky='ew', pady=5)
    row_idx += 1

    update_trigger_fields()
    # use lambda to avoid NameError if function reference not resolved yet
    tk.Button(control_frame, text="Démarrer l'Acquisition (ou F10)", command=lambda: start_acquisition_and_plot(None), font='Helvetica 12 bold', pady=5).grid(row=row_idx, column=0, columnspan=2, pady=10)

    # Plot area on the right
    plot_frame_container = tk.Frame(main_frame, bd=2, relief=tk.SUNKEN)
    plot_frame_container.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=10, pady=10)
    create_initial_plot_notebook(plot_frame_container)

    try:
        root.state('zoomed')
    except tk.TclError:
        try:
            root.attributes('-zoomed', True)
        except Exception:
            pass

    root.mainloop()

# ---------------------------
# Entry point
# ---------------------------

if __name__ == "__main__":
    setup_main_window()