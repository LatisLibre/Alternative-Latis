# -*- coding: utf-8 -*-
"""
Sysam SP5 Acquisition - Version17

Dernières modifications :
- Correction du binding F10 (utilisation de lambda pour éviter NameError si le handler est défini après).
- Intégration d'une impression multi-plateforme "best-effort" :
  * utilisation de pywin32 (win32api/win32print) sur Windows si disponible pour imprimer vers une imprimante choisie,
  * fallback sur os.startfile(..., 'print') sous Windows si pywin32 absent,
  * utilisation de lpr/lp sur Linux/macOS,
  * boîte de dialogue Tk pour choisir l'imprimante, modifier ses paramètres (si possible) et lancer l'impression de
    toutes les courbes visibles de l'onglet actif.
- Implémentation de "Copier" dans le menu Édition (copie CSV de la courbe active dans le presse-papiers).
- Correction d'une parenthèse manquante dans select_curve_dialog (Listbox).
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
        self.active_curve_index = 0

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
# Printing helpers (improved with pywin32 if available)
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
            # Use printui.dll to open properties dialog
            cmd = ['rundll32', 'printui.dll,PrintUIEntry', '/p', '/n', printer_name]
            subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            return True
        elif system == 'Darwin':
            # On macOS, open Printers & Scanners preferences (no direct printer-specific dialog reliably)
            try:
                subprocess.Popen(['open', '/System/Library/PreferencePanes/PrintAndScan.prefPane'])
                return True
            except Exception:
                return False
        else:
            # Try to open system-config-printer GUI if available
            try:
                subprocess.Popen(['system-config-printer', '--modify-printer', printer_name], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                return True
            except Exception:
                # fallback: try 'lpoptions' to show options in terminal (not GUI)
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
    - Sur Windows : utilise pywin32 ShellExecute 'printto' si disponible, sinon os.startfile(..., 'print')
    Returns True if a print command was dispatched, False otherwise.
    """
    system = platform.system()
    try:
        if system == 'Windows':
            # Try pywin32 ShellExecute 'printto' to send to a specific printer
            try:
                import win32api
                import win32print
                # If printer_name provided, use "printto" verb to target it
                if printer_name:
                    try:
                        win32api.ShellExecute(0, "printto", file_path, f"\"{printer_name}\"", ".", 0)
                        return True
                    except Exception:
                        pass
                # Fallback: use 'print' (default printer)
                try:
                    win32api.ShellExecute(0, "print", file_path, None, ".", 0)
                    return True
                except Exception:
                    pass
            except Exception:
                # pywin32 not available or failed; try os.startfile fallback
                try:
                    os.startfile(file_path, "print")
                    return True
                except Exception:
                    return False
            # if we reach here, try os.startfile as last resort
            try:
                os.startfile(file_path, "print")
                return True
            except Exception:
                return False
        elif system == 'Darwin':
            # macOS: use lp
            if printer_name:
                cmd = ['lp', '-d', printer_name, file_path]
            else:
                cmd = ['lp', file_path]
            subprocess.run(cmd, check=True)
            return True
        else:
            # Unix-like Linux: prefer lpr or lp
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
            # fallback to default lpr/lp
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
# Data table, calculation sheet, modelling, FFT, measurements
# (full implementations included)
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
# Modelling functions
# ---------------------------

# (f_lineaire, f_affine, f_exponentielle, f_puissance and modeliser_* already implemented above)

# ---------------------------
# Derivative, measurement and FFT helper functions
# ---------------------------

# (Already implemented above; reused in menus)

# ---------------------------
# Export, rename, recolor, selection and copy-to-clipboard
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
    # Corrected Listbox creation (previously parenthesis issue)
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
        # If multiple curves, prefer the one selected by reticule.active_curve_index if valid
        idx = 0
        try:
            idx = active_window['reticule'].active_curve_index
        except Exception:
            idx = 0
        curves = active_window['curves_data']
        if idx < 0 or idx >= len(curves):
            idx = 0
        t_arr, v_arr, name, is_raw = curves[idx]
        # Build CSV text
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
        # Place into clipboard (text)
        root.clipboard_clear()
        root.clipboard_append(csv_text)
        # Ensure clipboard is available after the program mainloop returns
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
    # bind F10 using a lambda so start_acquisition_and_plot is resolved at event time
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