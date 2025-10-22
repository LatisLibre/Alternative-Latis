# -*- coding: utf-8 -*-
import pycanum.main as pycan
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.animation as animation
from scipy.optimize import curve_fit 
import tkinter as tk
from tkinter import messagebox, filedialog 
from tkinter import ttk 
import sys as sys_module 
import csv 
import os 
import re 

# Import des composants pour l'intégration Matplotlib/Tkinter
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk

# --- CONFIGURATION GLOBALE ---
class Config:
    FE = 5000.0         # Fréquence d'échantillonnage en Hz (Calculée)
    DUREE = 0.02        # Durée totale d'acquisition en s (20 ms par défaut)
    CALIBRE = 10.0      # Calibre de l'entrée (V)
    N_POINTS = 100      # Nombre de points pour le mode NORMAL (Bloc)
    VOIE_ACQ = 0        # Voie d'acquisition (0 pour EA0)
    MODE_ACQUISITION = "Normal" 
    
    # Paramètres de Déclenchement
    MODE_DECLENCHEMENT = "Manuel" 
    VOIE_TRIG = 0       
    SEUIL = 0.0         
    PENTE = "Montante"  
    PRE_TRIG = 0        
    
    # Paramètre d'affichage par défaut (pour tous les onglets)
    PLOT_STYLE = "Points + Courbe" # Options: "Points", "Courbe seule", "Points + Courbe"
    DEFAULT_Y_MARGIN = 1.1 # Marge initiale pour l'axe Y par rapport au calibre

# --- VARIABLES GLOBALES ---
sysam_interface = None
CALIBRE_AFFICHE = Config.CALIBRE
ALL_CURVES = [] # Stocke (temps, tension, nom, is_raw_data) pour la fenêtre principale (Fenêtre 1)
N_POINTS_OSCILLO = 1000 
root = None 

# Variables globales pour l'interface utilisateur
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
plot_style_var = None # Variable pour le style d'affichage

# Liste globale pour stocker les grandeurs calculées (Nom, Unité, [t_data, v_data])
CALCULATED_CURVES = [] 

# --- CLASSE POUR LE RÉTICULE (CURSEURS INTERACTIFS) ---
class Reticule:
    """Gère l'affichage et l'interaction des curseurs sur le graphique Matplotlib."""
    # CHANGEMENT: Ajout de 'canvas' en paramètre pour le binding des événements
    def __init__(self, ax, fig, canvas, curves_data, calibre):
        self.ax = ax
        self.fig = fig
        self.canvas = canvas # Stocker le canvas
        self.curves_data = curves_data 
        self.calibre = calibre
        self.active_curve_index = 0 
        
        # Le texte des coordonnées est une annotation
        self.coord_text = ax.text(0.5, 1.05, '', 
                                  transform=ax.transAxes, 
                                  ha='center', fontsize=10, visible=False) 

        self.v_line = ax.axvline(x=0, color='r', linestyle='--', linewidth=0.8, visible=False)
        self.h_line = ax.axhline(y=0, color='b', linestyle='--', linewidth=0.8, visible=False)
        
        # CORRECTION: Lier l'événement directement au canvas Tkinter pour plus de robustesse
        self.cid_move = self.canvas.mpl_connect('motion_notify_event', self.on_mouse_move)
        
    def set_active_curve(self, index):
        """Définit l'index de la courbe que le réticule doit suivre."""
        if 0 <= index < len(self.curves_data):
            self.active_curve_index = index
            return True
        return False
        
    def on_mouse_move(self, event):
        if event.inaxes == self.ax and event.xdata is not None and self.curves_data:
            x = event.xdata 
            
            try:
                t_main, v_main, base_name, _ = self.curves_data[self.active_curve_index] 
            except IndexError:
                # Gestion des cas où l'index actif est invalide (réinitialisation à 0)
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
            
            # Correction: Assurer que le réticule devient visible au mouvement
            self.show_reticule()
            
            # Forcer le redessinage après chaque mouvement
            self.fig.canvas.draw_idle() 
        else:
            self.hide_reticule()
            
    def show_reticule(self):
        """Rend le réticule visible."""
        if not self.v_line.get_visible():
            self.v_line.set_visible(True)
            self.h_line.set_visible(True)
            self.coord_text.set_visible(True)

    def hide_reticule(self):
        """Cache le réticule et force le redessinage si l'état change."""
        # Correction: Appeler draw_idle seulement si le réticule était visible
        if self.v_line.get_visible(): 
            self.v_line.set_visible(False)
            self.h_line.set_visible(False)
            self.coord_text.set_visible(False)
            self.coord_text.set_text('')
            if self.fig.canvas:
                 self.fig.canvas.draw_idle()

# --- FONCTIONS DE GESTION DES FENÊTRES / ONGLET ACTIF ---

def get_active_plot_window():
    """Retourne l'objet de fenêtre (dict) pour l'onglet actuellement visible."""
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


def create_plot_in_frame(parent_frame, curves_data, title="Fenêtre Graphique", y_label="Tension (V)"):
    """Crée une figure Matplotlib dans un cadre Tkinter donné et retourne l'objet fenêtre."""
    fig, ax = plt.subplots(figsize=(6, 4), dpi=100)
    
    ax.set_title(title)
    ax.set_xlabel("Temps (s)")
    ax.set_ylabel(y_label) 
    
    # Limites initiales
    ax.set_xlim(0, Config.DUREE) 
    ax.set_ylim(-CALIBRE_AFFICHE * Config.DEFAULT_Y_MARGIN, CALIBRE_AFFICHE * Config.DEFAULT_Y_MARGIN)
    ax.grid(True)
    
    canvas = FigureCanvasTkAgg(fig, master=parent_frame)
    canvas_widget = canvas.get_tk_widget()
    canvas_widget.pack(side=tk.TOP, fill=tk.BOTH, expand=1)

    toolbar = NavigationToolbar2Tk(canvas, parent_frame)
    toolbar.update()
    canvas.draw()
    
    # CORRECTION: Passage de 'canvas' lors de l'initialisation du réticule
    reticule = Reticule(ax, fig, canvas, curves_data, CALIBRE_AFFICHE) 
    
    # Initialisation des limites précédentes (pour le décalibrage)
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
        '_initial_x_limits': x_lim_init, # Stockage des limites initiales
        '_initial_y_limits': y_lim_init  # Stockage des limites initiales
    }
    
    # Menu contextuel (clic droit)
    popup_menu = tk.Menu(canvas_widget, tearoff=0)
    
    # Calibrage auto et décalibrage
    popup_menu.add_command(label="Calibrage Auto (Optimiser l'Affichage)", command=lambda: auto_calibrate_plot(window_data))
    popup_menu.add_command(label="Décalibrer (Retour affichage initial)", command=lambda: de_calibrate_plot(window_data))
    popup_menu.add_separator()
    
    # Sous-menu Style d'affichage
    style_menu = tk.Menu(popup_menu, tearoff=0)
    style_options = ["Points", "Courbe seule", "Points + Courbe"]
    for style in style_options:
         style_menu.add_radiobutton(label=style, 
                                    command=lambda s=style, wd=window_data: update_plot_style(style=s, window_data=wd))
    popup_menu.add_cascade(label="Style d'Affichage", menu=style_menu)
    
    # Option Réticule lié à la courbe
    popup_menu.add_command(label="Réticule lié à la courbe...", command=lambda: select_reticule_curve(window_data))
    
    canvas_widget.bind("<Button-3>", lambda event: popup_menu.post(event.x_root, event.y_root))

    return window_data


def open_new_plot_window_tab(curves_to_plot=None, title_suffix=""):
    """Crée un nouvel onglet avec une fenêtre graphique. Peut recevoir une liste de courbes à tracer."""
    global plot_notebook, ALL_PLOT_WINDOWS
    
    new_tab_frame = tk.Frame(plot_notebook)
    new_curves_list = curves_to_plot if curves_to_plot is not None else []
    
    y_label = new_curves_list[0][2] if new_curves_list and "Temps" not in new_curves_list[0][2] else grandeur_physique_var.get()
    
    window_data = create_plot_in_frame(
        new_tab_frame, 
        new_curves_list, 
        title=f"Nouvelle Fenêtre {len(ALL_PLOT_WINDOWS) + 1} {title_suffix}",
        y_label=y_label
    )
    
    ALL_PLOT_WINDOWS.append(window_data)
    
    tab_name = f"Fenêtre {len(ALL_PLOT_WINDOWS)}"
    plot_notebook.add(new_tab_frame, text=tab_name)
    plot_notebook.select(new_tab_frame)
    
    # Rafraîchir l'affichage avec le style par défaut
    plot_mode_unique(window_data) 
    
    if new_curves_list:
        # Calibrage automatique des nouvelles données
        auto_calibrate_plot(window_data) 
    
    return window_data

# --- FONCTIONS UTILITAIRES ET D'OUTILS (Non modifiées) ---

def close_program():
    """Ferme proprement la fenêtre Tkinter et arrête l'application."""
    if root:
        root.destroy()
    sys_module.exit(0) 

def reset_acquisition_params():
    """Réinitialise les paramètres d'acquisition à leur valeur par défaut."""
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
    grandeur_physique_var.set("Tension (V)")
    voie_trig_var.set(f"EA{Config.VOIE_TRIG}")
    seuil_var.set(str(Config.SEUIL))
    pente_var.set(Config.PENTE)
    pre_trig_var.set(str(Config.PRE_TRIG))
    
    update_fe_and_xaxis()
    update_trigger_fields()


def menu_nouveau():
    """Réinitialise les paramètres et ouvre un nouvel onglet graphique."""
    global ALL_PLOT_WINDOWS
    
    reset_acquisition_params()
    
    new_window = open_new_plot_window_tab()
    
    new_window['curves_data'].clear()
    plot_mode_unique(new_window)
    
    messagebox.showinfo("Nouveau", "Paramètres d'acquisition réinitialisés et nouvel onglet graphique créé.")


def update_fe_and_xaxis(event=None):
    """Met à jour Fe = N / Delta_t et l'affichage de l'axe X sur tous les onglets."""
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
            if window['ax'] and window['canvas']:
                # Mise à jour des limites X
                current_y_lim = window['ax'].get_ylim()
                window['ax'].set_xlim(0, duree)
                window['ax'].set_ylim(current_y_lim)
                
                # Mise à jour des limites initiales et précédentes
                window['_initial_x_limits'] = (0, duree) 
                window['_previous_x_limits'] = (0, duree) 
                
                window['canvas'].draw_idle()
                
    except ValueError as e:
        pass

def menu_ouvrir():
    """Ouvre un fichier CSV exporté précédemment et charge les données dans l'onglet ACTIF."""
    global duree_var, superposition_var, CALIBRE_AFFICHE
    
    active_window = get_active_plot_window()
    if not active_window:
        messagebox.showwarning("Erreur", "Aucun panneau graphique actif trouvé.")
        return

    active_curves = active_window['curves_data']
    
    try:
        filepath = filedialog.askopenfilename(
            filetypes=[("Fichiers CSV", "*.csv")],
            title="Ouvrir un fichier de données"
        )
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
                    if not active_curves:
                       grandeur_physique_var.set(curve_name)
                         
                except IndexError:
                    curve_name = "Données Importées (V)"

            for i, row in enumerate(reader):
                if len(row) >= 2:
                    try:
                        t = float(row[0].replace(',', '.'))
                        v = float(row[1].replace(',', '.'))
                        temps_list.append(t)
                        tension_list.append(v)
                    except ValueError:
                        print(f"Avertissement: Ligne {i+2} ignorée (format incorrect).")
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
            Config.DUREE = temps_data.max()
            duree_var.set(f"{Config.DUREE:.3f}")
            update_fe_and_xaxis() 
            
        new_calibre = np.ceil(np.max(np.abs(tension_data)) * 1.1)
        if new_calibre == 0: new_calibre = 10.0 
        CALIBRE_AFFICHE = new_calibre 
            
        if len(active_curves) == 1 or not superposition_var.get():
             active_window['ax'].set_ylabel(curve_display_name)
             
        plot_mode_unique(active_window)
        
        # NOUVEAU: Calibrage automatique après l'ouverture
        auto_calibrate_plot(active_window) 
        
        messagebox.showinfo("Ouverture réussie", f"Données '{curve_display_name}' chargées avec {len(temps_data)} points dans l'onglet actif.")

    except Exception as e:
        messagebox.showerror("Erreur d'Ouverture", f"Impossible d'ouvrir ou de lire le fichier: {e}")
        

def select_curve_dialog(active_window, title="Sélection de la courbe"):
    """
    Ouvre une boîte de dialogue pour sélectionner une courbe à partir
    de la liste dans l'onglet actif.
    Retourne (index, t_data, v_data, base_name, is_raw_data) ou None.
    """
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

    listbox = tk.Listbox(selection_window, width=50, height=len(curves_list))
    
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
    
def select_reticule_curve(window_data=None):
    """Ouvre une boîte de dialogue pour choisir la courbe que le réticule doit suivre."""
    if window_data is None:
        window_data = get_active_plot_window()
        
    if not window_data or not window_data['curves_data']:
        messagebox.showwarning("Réticule", "Aucune courbe n'est disponible dans l'onglet actif.")
        return
        
    curves_list = window_data['curves_data']
    
    selection_window = tk.Toplevel(root)
    selection_window.title("Réticule lié à la courbe")
    
    tk.Label(selection_window, text="Choisir la courbe pour le réticule :", font='Helvetica 10 bold', padx=10, pady=10).pack()

    listbox = tk.Listbox(selection_window, width=50, height=len(curves_list))
    
    for i, (_, _, name, is_raw) in enumerate(curves_list):
        data_type = "(Acquisition/Importation)" if is_raw else "(Calcul/Modèle)"
        listbox.insert(tk.END, f"[{i+1}] {name} {data_type}")
        
    listbox.pack(padx=10, pady=5)
    
    # Sélectionne l'index actuel si valide
    current_index = window_data['reticule'].active_curve_index
    if current_index < len(curves_list):
        listbox.selection_set(current_index)
        listbox.see(current_index)
        
    def on_select():
        try:
            index = listbox.curselection()[0]
            
            # Mise à jour de l'index dans l'objet Reticule
            if window_data['reticule'].set_active_curve(index):
                # Mise à jour du label de l'axe Y pour correspondre à la courbe principale/reticule
                window_data['ax'].set_ylabel(curves_list[index][2])
                window_data['canvas'].draw_idle()
                
                messagebox.showinfo("Réticule", f"Réticule lié à la courbe : {curves_list[index][2]}")
            selection_window.destroy()
            
        except IndexError:
            messagebox.showwarning("Sélection", "Veuillez sélectionner une courbe.")
            
    tk.Button(selection_window, text="Confirmer la sélection", command=on_select, pady=5).pack(pady=10)
    listbox.bind('<Double-1>', lambda event: on_select())
    
    root.wait_window(selection_window)


def calculer_derivee():
    """Calcul de la dérivée de la courbe choisie dans l'onglet ACTIF."""
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
    
    # Mise à jour et calibrage auto après l'ajout d'une courbe calculée
    plot_mode_unique(active_window)
    auto_calibrate_plot(active_window) 


def exporter_csv():
    """Exporte toutes les courbes stockées dans l'onglet ACTIF dans un fichier CSV."""
    active_window = get_active_plot_window()
    if not active_window or not active_window['curves_data']:
        messagebox.showwarning("Exportation", "Aucune donnée acquise dans l'onglet actif à exporter.")
        return
        
    ALL_CURVES_ACTIVE = active_window['curves_data']
        
    try:
        filepath = filedialog.asksaveasfilename(
            defaultextension=".csv",
            filetypes=[("Fichiers CSV", "*.csv")],
            title="Exporter les données des courbes de l'onglet actif"
        )
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

def menu_enregistrer():
    messagebox.showinfo("Fonctionnalité", "La fonction Enregistrer (Fichier) sera implémentée ici.")
def menu_copier():
    messagebox.showinfo("Fonctionnalité", "La fonction Copier (Édition) sera implémentée ici.")
    
def show_about_info():
    """Affiche la fenêtre À propos avec les informations mises à jour."""
    info = (
        "Projet d'acquisition Sysam SP5 - Alternative Libre LatisPro\n\n"
        "**Auteur** : Mathias Laroche - Lycée Lafayette Clermont Ferrand\n" 
        "**Contact** : mathias.laroche@ac-clermont.fr\n\n"
        "Projet réalisé avec les outils GNU Linux Mint , Python3 et Spyder\n\n" 
        "**Licence** : GPL"
    )
    messagebox.showinfo("À propos", info)

def show_help_file():
    """Affiche une fenêtre avec la liste complète des fonctionnalités du programme, formatée avec un sommaire."""
    help_content = """
## 📚 GUIDE D'UTILISATION - SYSAM SP5 (ALTERNATIVE LATISPRO)

Ce guide décrit l'ensemble des fonctionnalités disponibles pour l'acquisition et le traitement des données.

---------------------------------------------------
### I. SOMMAIRE
---------------------------------------------------
1.  **ACQUISITION ET CONFIGURATION**
    * Mode et Paramètres
    * Déclenchement
2.  **AFFICHAGE GRAPHIQUE ET ERGONOMIE**
    * Réticule (Curseurs)
    * Calibrage et Décalibrage
    * Styles d'Affichage
3.  **OUTILS DE TRAITEMENT ET CALCULS**
    * Fichier et Exportation
    * Calculs (Dérivée, Formules)
    * Modélisation (Ajustement par courbe)

---------------------------------------------------
### 1. ACQUISITION ET CONFIGURATION
---------------------------------------------------
#### 1.1 Mode et Paramètres
* **Mode Normal :** Acquisition par **bloc unique**. Utilisé pour les expériences courtes.
* **Mode Permanent :** Mode **oscilloscope** (rafraîchissement constant). S'ouvre dans une fenêtre séparée.
* **Voie d'Acquisition :** Choix de l'entrée (EA0 à EA7).
* **Calibre (V) :** Fixe la plage maximale de tension ($ \pm V_{calibre} $).
* **Durée Totale ($\Delta t$) / Nbre de Points (N) :** Définissent la plage temporelle et la résolution. La Fréquence d'Échantillonnage ($F_e = N / \Delta t$) est calculée automatiquement.
* **Grandeur :** Permet de nommer les axes Y et de définir l'unité (ex: Intensité (A)).
* **Superposer :** Permet d'ajouter la nouvelle acquisition à celles déjà tracées dans l'onglet.

#### 1.2 Déclenchement
* **Manuel :** Lancement immédiat de l'acquisition.
* **Automatique sur seuil :** L'acquisition démarre lorsque la tension d'une voie de déclenchement ($EA_x$) franchit un **Seuil** selon une **Pente** (Montante ou Descendante).
* **Pré-trig (%) :** Pourcentage de points enregistrés *avant* le moment du déclenchement.

---------------------------------------------------
### 2. AFFICHAGE GRAPHIQUE ET ERGONOMIE
---------------------------------------------------

#### 2.1 Réticule (Curseurs) 🎯
* Le **réticule** (lignes croisées et affichage des coordonnées) s'active lorsque la souris survole la zone graphique.
* **Liaison à la courbe :** L'option `Réticule lié à la courbe...` du menu contextuel (clic droit) permet de choisir quelle courbe le réticule doit suivre pour afficher ses coordonnées avec précision.

#### 2.2 Calibrage et Décalibrage 📐
* **Calibrage Auto :** (Menu Options ou Clic Droit) Optimise les limites des axes pour que toutes les courbes visibles occupent au mieux l'espace du graphique. **Lancé automatiquement** après chaque nouvelle acquisition ou chargement de fichier.
* **Décalibrer :** (Menu Options ou Clic Droit) Annule le dernier calibrage auto et revient aux **limites d'axes précédentes** (ou aux limites initiales/par défaut si le graphe n'a jamais été calibré).

#### 2.3 Styles d'Affichage
* (Menu Options ou Clic Droit) Permet de choisir entre **Points**, **Courbe seule**, ou **Points + Courbe** pour le tracé des données brutes (acquisition/importation).

---------------------------------------------------
### 3. OUTILS DE TRAITEMENT ET CALCULS
---------------------------------------------------

#### 3.1 Fichier et Exportation
* **Fichier > Ouvrir :** Charge des données depuis un fichier CSV. **Calibrage automatique** immédiat.
* **Fichier > Exporter (CSV) :** Exporte *toutes* les courbes présentes dans l'onglet actif (temps et valeurs) dans un fichier CSV standard.

#### 3.2 Calculs (Dérivée et Formules)
* **Outils > Calculer dérivée (dY/dt) :** Calcule numériquement la dérivée ($\frac{\Delta Y}{\Delta t}$) de la courbe sélectionnée et l'ajoute au graphique actif.
* **Outils > Feuille de calcul :** Ouvre une fenêtre pour appliquer des formules mathématiques (utilisant `numpy`) aux données existantes (par exemple, $U^2/R$ ou $np.sin(t)$) et afficher le résultat sur un nouvel onglet.

#### 3.3 Modélisation (Ajustement par courbe)
* **Outils > Modélisation > [...] :** Permet d'ajuster une courbe expérimentale avec un modèle mathématique (Linéaire, Affine, Exponentiel, Puissance) par minimisation de l'erreur (méthode des moindres carrés).
* Les résultats de l'ajustement sont affichés dans une fenêtre avec les paramètres et leurs unités.
* Le modèle ajusté est tracé sur le graphique.
    """
    help_window = tk.Toplevel(root)
    help_window.title("Aide du programme - Fonctionnalités")
    
    # Utilisation d'un Text widget pour un meilleur rendu
    text_widget = tk.Text(help_window, wrap=tk.WORD, padx=15, pady=15, font=('Consolas', 10), bg='#f8f8f8')
    text_widget.pack(expand=True, fill='both')
    
    # Insertion du contenu avec des tags pour le formatage (similaire au Markdown)
    text_widget.insert(tk.END, help_content)
    
    text_widget.config(state=tk.DISABLED)

# --- Fonctions de Modélisation (MATHÉMATIQUES) (Non modifiées) ---

def f_lineaire(x, a):
    return a * x

def f_affine(x, a, b):
    return a * x + b

def f_exponentielle(x, A, tau, C):
    return A * np.exp(-x / tau) + C

def f_puissance(x, A, n, B):
    # Assurez-vous que x > 0 pour x**n, sinon on ajoute un petit epsilon
    x_safe = np.array([max(1e-9, xi) for xi in x])
    return A * (x_safe ** n) + B

# --- Fonctions de Modélisation (RÉSULTATS) (Non modifiées) ---
def show_model_results(model_type, params, units, equation):
    """Affiche les résultats de la modélisation dans une nouvelle fenêtre."""
    dialog = tk.Toplevel()
    dialog.title(f"Résultats Modélisation {model_type}")
    
    dialog.update_idletasks()
    width = 400
    height = 200 + 30 * len(params)
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
             
    tk.Button(dialog, text="OK", command=dialog.destroy).pack(pady=10)

def get_units_for_model(curve_name_with_unit):
    """Détermine les unités Y et X à partir du label de la courbe."""
    unite_y = "U.A."
    if '(' in curve_name_with_unit and ')' in curve_name_with_unit:
        unite_y = curve_name_with_unit.split('(')[-1].replace(')', '').strip()
    unite_x = 's'
    return unite_y, unite_x

# --- Fonctions de Modélisation (avec sélection) (Non modifiées) ---

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
        
        # Mise à jour et calibrage auto après l'ajout d'une courbe calculée
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
        
        params = {'a': (a, 'Coeff. directeur'), 'b': (b, 'Ordonnée à l\'origine')}
        units = {'a': f"{unite_y}/{unite_x}", 'b': unite_y}
        equation = "Y = a * X + b"
        
        show_model_results('Affine', params, units, equation)
        
        model_name = f"Modèle Affine (y={a:.2e}x + {b:.2e})"
        active_curves.append((t_data, v_modele, model_name, False)) 
        
        # Mise à jour et calibrage auto après l'ajout d'une courbe calculée
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
        tau0 = t_data[-1] / 3
        p0 = [A0, tau0, C0]

        popt, pcov = curve_fit(f_exponentielle, t_data, v_data, p0=p0, maxfev=5000)
        A, tau, C = popt
        v_modele = f_exponentielle(t_data, A, tau, C)
        
        unite_y, unite_x = get_units_for_model(base_name)
        
        params = {
            'A': (A, 'Amplitude initiale'), 
            'tau': (tau, 'Constante de temps'),
            'C': (C, 'Offset (valeur finale)')
        }
        units = {'A': unite_y, 'tau': unite_x, 'C': unite_y}
        equation = u"Y = A \u00B7 exp(-X/\u03C4) + C"
        
        show_model_results('Exponentielle', params, units, equation)
        
        model_name = f"Modèle Exp. (A={A:.2e}, \u03C4={tau:.2e})"
        active_curves.append((t_data, v_modele, model_name, False)) 
        
        # Mise à jour et calibrage auto après l'ajout d'une courbe calculée
        plot_mode_unique(active_window)
        auto_calibrate_plot(active_window) 
        
    except RuntimeError:
         messagebox.showerror("Erreur Modélisation Exp.", "Ajustement non optimal: Vérifiez la forme des données ou réduisez la zone d'ajustement.")
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
        
        params = {
            'A': (A, 'Coeff. multiplicateur'), 
            'n': (n, 'Exposant'),
            'B': (B, 'Offset')
        }
        units = {'A': unite_A, 'n': 'sans unité', 'B': unite_y}
        equation = u"Y = A \u00B7 X^n + B"
        
        show_model_results('Puissance', params, units, equation)
        
        model_name = f"Modèle Puissance (y={A:.2e}x^{n:.2f} + {B:.2e})"
        active_curves.append((t_data, v_modele, model_name, False)) 
        
        # Mise à jour et calibrage auto après l'ajout d'une courbe calculée
        plot_mode_unique(active_window)
        auto_calibrate_plot(active_window) 
        
    except RuntimeError:
         messagebox.showerror("Erreur Modélisation Pui.", "Ajustement non optimal: Vérifiez la forme des données.")
    except Exception as e:
        messagebox.showerror("Erreur Modélisation Pui.", f"Erreur: {e}")

# --- FONCTION DE CALIBRAGE AUTOMATIQUE (Non modifiée) ---
def auto_calibrate_plot(window_data=None):
    """
    Recalcule les limites des axes X et Y pour optimiser l'affichage
    des courbes stockées dans la fenêtre graphique.
    Sauvegarde les limites actuelles AVANT le calibrage.
    """
    global CALIBRE_AFFICHE
    
    if window_data is None:
        window_data = get_active_plot_window()
        if window_data is None:
            return

    curves_data = window_data['curves_data']
    ax = window_data['ax']
    
    # 1. Stocker les limites actuelles AVANT le calibrage (pour le décalibrage)
    window_data['_previous_x_limits'] = ax.get_xlim()
    window_data['_previous_y_limits'] = ax.get_ylim()
    
    if not curves_data:
        # Réinitialisation aux valeurs initiales par défaut si aucune courbe
        ax.set_xlim(window_data['_initial_x_limits'])
        ax.set_ylim(window_data['_initial_y_limits'])
        window_data['canvas'].draw_idle()
        return

    # 2. Calibrage de l'axe X (Temps)
    all_t = np.concatenate([t for t, v, nom, _ in curves_data if t.size > 0])
    if all_t.size > 0:
        t_min = all_t.min()
        t_max = all_t.max()
        # Marge de 5% de la durée totale
        t_range = t_max - t_min
        if t_range > 0:
             margin_x = t_range * 0.05 
             x_min = t_min - margin_x
             x_max = t_max + margin_x
             
             # S'assurer que les limites ne sont pas inversées
             if x_min >= x_max: 
                 x_min, x_max = t_min - 0.001, t_max + 0.001
                 
        else: # Cas où tous les points ont le même temps (signal constant)
             x_min, x_max = t_min - 0.001, t_max + 0.001
    else:
        x_min, x_max = window_data['_initial_x_limits']
        
    ax.set_xlim(x_min, x_max)

    # 3. Calibrage de l'axe Y (Grandeur)
    all_v = np.concatenate([v for t, v, nom, _ in curves_data if v.size > 0])
    if all_v.size > 0:
        v_min = all_v.min()
        v_max = all_v.max()
        
        v_range = v_max - v_min
        
        # Marge de 10% de la plage totale
        if v_range > 0:
             margin_y = v_range * 0.10 
             y_min = v_min - margin_y
             y_max = v_max + margin_y
             
             # S'assurer que les limites ne sont pas inversées
             if y_min >= y_max: 
                 y_min = v_min - np.abs(v_min) * 0.1 if v_min != 0 else -1
                 y_max = v_max + np.abs(v_max) * 0.1 if v_max != 0 else 1
                 
        else: # Si le signal est constant
             y_min = v_min - np.abs(v_min) * 0.1 if v_min != 0 else -1
             y_max = v_max + np.abs(v_max) * 0.1 if v_max != 0 else 1
             
    else:
        # Fallback pour un graphique vide
        y_min, y_max = window_data['_initial_y_limits']
        
    ax.set_ylim(y_min, y_max)
    
    window_data['canvas'].draw_idle()
    
# --- FONCTION DE DÉCALIBRAGE (Non modifiée) ---
def de_calibrate_plot(window_data=None):
    """
    Rétablit les limites d'axe X et Y aux valeurs stockées
    avant le dernier calibrage, ou aux valeurs initiales par défaut si aucune.
    """
    if window_data is None:
        window_data = get_active_plot_window()
        if window_data is None:
            messagebox.showwarning("Décalibrage", "Aucun panneau graphique actif trouvé.")
            return

    ax = window_data['ax']
    
    # Rétablir les limites précédentes
    x_min, x_max = window_data['_previous_x_limits']
    y_min, y_max = window_data['_previous_y_limits']
    
    # Si les limites précédentes sont les mêmes que les limites initiales,
    # cela signifie qu'il n'y a pas eu d'opération de calibrage ou que l'on
    # tente de décalibrer plusieurs fois. On utilise donc les limites initiales.
    if (x_min, x_max) == window_data['_initial_x_limits'] and \
       (y_min, y_max) == window_data['_initial_y_limits']:
         
         # Si le graphe est déjà décalibré/initial, on ne fait rien
         if ax.get_xlim() == window_data['_initial_x_limits'] and \
            ax.get_ylim() == window_data['_initial_y_limits']:
              messagebox.showinfo("Décalibrage", "Le graphique est déjà à ses limites initiales.")
              return
              
         # Sinon, on utilise les limites initiales
         x_min, x_max = window_data['_initial_x_limits']
         y_min, y_max = window_data['_initial_y_limits']
         
    
    ax.set_xlim(x_min, x_max)
    ax.set_ylim(y_min, y_max)
    
    # Stocker les limites initiales comme limites précédentes pour la prochaine opération
    window_data['_previous_x_limits'] = window_data['_initial_x_limits']
    window_data['_previous_y_limits'] = window_data['_initial_y_limits']
    
    window_data['canvas'].draw_idle()


# --- FONCTIONS DE MISE À JOUR DE LA GRAPHIQUE ---

def update_plot_label(event=None):
    """Met à jour le label Y sur la première courbe (principale) si elle est basée sur Tension(V)."""
    for window in ALL_PLOT_WINDOWS:
        if window['ax'] and window['canvas']:
            if len(window['curves_data']) == 0:
                 window['ax'].set_ylabel(grandeur_physique_var.get())
                 window['canvas'].draw_idle()

# --- Fonctions du Tableau de Données (pour modification) (Non modifiées) ---
def open_data_table():
    """Ouvre une nouvelle fenêtre avec une courbe sélectionnée dans un tableau consultable/modifiable."""
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
    # Cette fonction nécessiterait une librairie de tableau comme pandas ou une implémentation Tkinter plus complexe
    messagebox.showinfo("Fonctionnalité", "Le Tableau des valeurs (Tableau des valeurs expérimentales) sera implémenté ici.")
    pass


# --- FONCTIONS DE LA FEUILLE DE CALCUL (GRANDEURS CALCULÉES) (Non modifiées) ---

def open_calcul_sheet():
    """Ouvre une fenêtre pour créer de nouvelles grandeurs à partir de formules."""
    global CALCULATED_CURVES
    
    active_window = get_active_plot_window()
    if not active_window:
         messagebox.showwarning("Erreur", "Veuillez d'abord effectuer une acquisition ou charger des données.")
         return
         
    available_data = {}
    if active_window['curves_data']:
        # Utilisez le temps de la première courbe comme temps de référence
        base_t_data = active_window['curves_data'][0][0] 
        available_data['t'] = (base_t_data, "s") 
    else:
        messagebox.showwarning("Erreur", "Aucune donnée de base (Temps) trouvée dans l'onglet actif.")
        return
        
    base_time_length = len(available_data['t'][0])
    
    for t_data, v_data, name, _ in active_window['curves_data']:
        var_name = name.split('(')[0].strip().replace(' ', '_').replace('-', '_')
        unit = name.split('(')[-1].replace(')', '').strip() if '(' in name else "V" 
        
        # N'ajouter que les vecteurs qui ont la même longueur que le vecteur temps de base
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
        vars_list_text += f"  - **{name}** (Unité: {unit})\n"
    
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
        """Exécute la formule, stocke la nouvelle grandeur, et l'affiche sur un nouvel onglet."""
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
            
            curves_to_plot = [
                (available_data['t'][0], result_array, full_name, False) 
            ]
            
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


def create_initial_plot_notebook(parent_frame):
    """Crée le conteneur à onglets et le premier onglet principal."""
    global plot_notebook, ALL_PLOT_WINDOWS
    
    plot_notebook = ttk.Notebook(parent_frame)
    plot_notebook.pack(side=tk.TOP, fill=tk.BOTH, expand=1)

    main_tab_frame = tk.Frame(plot_notebook)
    plot_notebook.add(main_tab_frame, text="Fenêtre 1 (Principale)")
    
    initial_window = create_plot_in_frame(main_tab_frame, ALL_CURVES, 
                                          title="Acquisition Normal (Bloc) - Principale",
                                          y_label=grandeur_physique_var.get())
    
    ALL_PLOT_WINDOWS.append(initial_window)


def plot_mode_unique(window_data=None):
    """Met à jour la fenêtre graphique spécifique (l'onglet actif par défaut) avec le style d'affichage choisi."""
    global CALIBRE_AFFICHE
    
    if window_data is None:
        window_data = get_active_plot_window()
        if window_data is None:
            return

    ax = window_data['ax']
    canvas = window_data['canvas']
    curves_data = window_data['curves_data']
    reticule = window_data['reticule']
    
    # Le style d'affichage est récupéré via la variable globale (mise à jour par le menu/clic droit)
    plot_style = plot_style_var.get()
    
    # Stocker les limites actuelles AVANT le clear (pour le décalibrage)
    current_x_lim = ax.get_xlim()
    current_y_lim = ax.get_ylim()

    if current_x_lim != window_data['_initial_x_limits'] or \
       current_y_lim != window_data['_initial_y_limits']:
       window_data['_previous_x_limits'] = current_x_lim
       window_data['_previous_y_limits'] = current_y_lim

    x_min, x_max = current_x_lim
    y_min, y_max = current_y_lim
    
    ax.clear()

    # Rétablir les limites après clear()
    if current_x_lim == window_data['_initial_x_limits'] and \
       current_y_lim == window_data['_initial_y_limits']:
        ax.set_xlim(window_data['_initial_x_limits'])
        ax.set_ylim(window_data['_initial_y_limits'])
    else:
        ax.set_xlim(x_min, x_max)
        ax.set_ylim(y_min, y_max)
    
    # Réattacher le Reticule à l'AXE et mettre à jour ses données
    reticule.ax = ax 
    reticule.curves_data = curves_data
    
    # Rattachage des artistes (nécessaire après ax.clear())
    # Note: On utilise `ax.artists` pour vérifier s'ils sont déjà présents
    if reticule.v_line not in ax.artists: 
        ax.add_artist(reticule.v_line)
    if reticule.h_line not in ax.artists:
        ax.add_artist(reticule.h_line)
    if reticule.coord_text not in ax.artists:
         ax.add_artist(reticule.coord_text)
    
    # Rétablissement du transform pour le texte
    reticule.coord_text.set_transform(ax.transAxes) 
    
    # Déterminer le label Y à partir de la courbe active du réticule
    grandeur_nom_y = grandeur_physique_var.get()
    if curves_data:
        try:
            active_index = reticule.active_curve_index
            if 0 <= active_index < len(curves_data):
                grandeur_nom_y = curves_data[active_index][2]
        except:
            grandeur_nom_y = curves_data[0][2]
        
    ax.set_title(f"Acquisition (Bloc) - Superposition de {len(curves_data)} courbes")
    ax.set_xlabel("Temps (s)")
    ax.set_ylabel(grandeur_nom_y) 
    
    ax.grid(True)
    
    if curves_data:
        for i, (t, v, nom, is_raw) in enumerate(curves_data):
            color = plt.cm.viridis(i / len(curves_data))
            
            # Courbes calculées/modélisées (toujours en ligne pointillée, sans marqueur)
            if not is_raw:
                linecolor = 'red' if 'Modèle' in nom else ('blue' if 'Dérivée' in nom or 'Calcul' in nom else color) 
                ax.plot(t, v, label=nom, color=linecolor, linestyle='--', linewidth=2)
            
            # Données brutes (Acquisition/Importation)
            else:
                linecolor = color
                
                # NOUVEAU: Utilisation du marqueur '+' pour la croix
                marker = '+' if plot_style in ["Points", "Points + Courbe"] else '' 
                # Ligne reliant les points
                linestyle = '-' if plot_style in ["Courbe seule", "Points + Courbe"] else 'None'

                if len(t) > 0 and len(v) > 0:
                    ax.plot(t, v, 
                            label=nom, 
                            color=linecolor, 
                            linestyle=linestyle, 
                            marker=marker, 
                            markersize=6, 
                            linewidth=1)

        ax.legend()
    
    canvas.draw_idle()

def update_plot_style(event=None, style=None, window_data=None):
    """Met à jour le style d'affichage du graphique actif lorsque la variable change."""
    
    if window_data is None:
        window_data = get_active_plot_window()
    
    if style is not None:
         plot_style_var.set(style) 
         
    if window_data:
         plot_mode_unique(window_data)


# --- Fonctions restantes (Acquisition, Oscillo, etc.) (Non modifiées) ---

def plot_mode_permanent():
    # ... (Code pour le mode permanent inchangé)
    messagebox.showwarning("Attention", "Le mode Permanent (Oscilloscope) n'est pas adapté à la gestion par onglets et s'ouvrira dans une fenêtre séparée.")
    
    global sysam_interface, CALIBRE_AFFICHE
    
    fig, ax = plt.subplots()

    grandeur_nom = grandeur_physique_var.get() 
    
    titre = f"Mode Permanent (Oscillo) - EA{Config.VOIE_ACQ} à {Config.FE:.0f} Hz"
    if Config.MODE_DECLENCHEMENT == "Automatique sur seuil":
        titre += f" (Déclenchement Seuil sur EA{Config.VOIE_TRIG})"
        
    ax.set_title(titre)
    ax.set_xlabel("Temps (s)")
    ax.set_ylabel(grandeur_nom) 
    ax.set_ylim(-CALIBRE_AFFICHE * Config.DEFAULT_Y_MARGIN, CALIBRE_AFFICHE * Config.DEFAULT_Y_MARGIN)
    ax.grid(True)
    
    line, = init_oscillo(ax) 
    
    ani = animation.FuncAnimation(
        fig, 
        update_oscillo, 
        fargs=(sysam_interface, ax, line), 
        interval=50, 
        blit=True
    ) 

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
    """Démarre l'acquisition et affiche les résultats dans l'onglet ACTIF."""
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
        
        grandeur_nom_defaut = grandeur_physique_var.get()
        
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
            sysam_interface.config_declenchement(
                Config.VOIE_TRIG, Config.SEUIL, pente_val, Config.PRE_TRIG
            )
        
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
            
            # NOUVEAU: Calibrage automatique après l'acquisition réussie
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

def update_trigger_fields(*args):
    """Active ou désactive les champs de déclenchement selon le mode choisi."""
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
        widget.config(state=state)
    for label in labels_to_color:
        label.config(fg=fg_color)

def setup_main_window():
    # ... (Initialisation des variables globales)
    global root, grandeur_physique_var, duree_var, superposition_var
    global nb_points_var, calibre_var, voie_acq_var, mode_declenchement_var
    global mode_acquisition_var, fe_display_var
    global voie_trig_var, seuil_var, pente_var, pre_trig_var
    global menu_voie_trig, entry_seuil, menu_pente, entry_pre_trig
    global label_voie_trig, label_seuil, label_pente, label_pre_trig
    global plot_style_var
    
    root = tk.Tk()
    root.title("Acquisition Sysam SP5 - Alternative LatisPro")
    
    root.protocol("WM_DELETE_WINDOW", close_program)
    root.bind('<F10>', start_acquisition_and_plot) 

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


    # --- BARRE DE MENU ---
    menubar = tk.Menu(root)
    root.config(menu=menubar)
    
    file_menu = tk.Menu(menubar, tearoff=0)
    menubar.add_cascade(label="Fichier", menu=file_menu)
    file_menu.add_command(label="Nouveau", command=menu_nouveau)
    file_menu.add_command(label="Ouvrir...", command=menu_ouvrir)
    file_menu.add_command(label="Enregistrer...", command=menu_enregistrer)
    file_menu.add_command(label="Exporter (CSV)...", command=exporter_csv) 
    file_menu.add_separator()
    file_menu.add_command(label="Quitter", command=close_program) 

    edit_menu = tk.Menu(menubar, tearoff=0)
    menubar.add_cascade(label="Édition", menu=edit_menu)
    edit_menu.add_command(label="Copier", command=menu_copier)

    tools_menu = tk.Menu(menubar, tearoff=0)
    menubar.add_cascade(label="Outils", menu=tools_menu)
    tools_menu.add_command(label="Nouvelle fenêtre graphique (Onglet)", command=open_new_plot_window_tab) 
    tools_menu.add_command(label="Tableau des valeurs expérimentales", command=open_data_table) 
    tools_menu.add_command(label="Feuille de calcul (Nouvelles Grandeurs)", command=open_calcul_sheet) 
    tools_menu.add_separator()
    tools_menu.add_command(label="Calculer dérivée (dY/dt)", command=calculer_derivee) 
    
    model_menu = tk.Menu(tools_menu, tearoff=0)
    tools_menu.add_cascade(label="Modélisation", menu=model_menu) 
    model_menu.add_command(label="Linéaire (y = ax)", command=modeliser_lineaire)
    model_menu.add_command(label="Affine (y = ax + b)", command=modeliser_affine)
    model_menu.add_command(label="Exponentielle (y = A·exp(-t/τ) + C)", command=modeliser_exponentielle) 
    model_menu.add_command(label="Puissance (y = A·tⁿ + B)", command=modeliser_puissance) 
    
    # Menu Options (contient les options graphiques principales)
    options_menu = tk.Menu(menubar, tearoff=0)
    menubar.add_cascade(label="Options", menu=options_menu)
    
    options_menu.add_command(label="Calibrage Auto (Optimiser l'Affichage)", command=lambda: auto_calibrate_plot()) 
    options_menu.add_command(label="Décalibrer (Retour affichage initial)", command=lambda: de_calibrate_plot()) 
    options_menu.add_command(label="Réticule lié à la courbe...", command=lambda: select_reticule_curve())
    options_menu.add_separator()
    
    # Sous-menu pour le style d'affichage
    display_style_menu = tk.Menu(options_menu, tearoff=0)
    options_menu.add_cascade(label="Style d'Affichage", menu=display_style_menu)
    
    style_options = ["Points", "Courbe seule", "Points + Courbe"]
    for style in style_options:
         display_style_menu.add_radiobutton(label=style, 
                                            command=lambda s=style: update_plot_style(style=s))


    help_menu = tk.Menu(menubar, tearoff=0)
    menubar.add_cascade(label="Aide", menu=help_menu)
    help_menu.add_command(label="Fichier d'aide (Fonctionnalités)", command=show_help_file)
    help_menu.add_separator()
    help_menu.add_command(label="À propos", command=show_about_info)


    # --- CADRE DE CONFIGURATION (GAUCHE) ---
    main_frame = tk.Frame(root)
    main_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True) 
    
    control_frame = tk.Frame(main_frame, padx=15, pady=15, bd=2, relief=tk.GROOVE)
    control_frame.pack(side=tk.LEFT, fill=tk.Y, padx=10, pady=10)
    
    row_idx = 0
    
    # Section MODE D'ACQUISITION
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
    
    # Section ÉCHANTILLONNAGE / CALIBRE
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
    
    # Section DÉCLENCHEMENT
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

    tk.Button(control_frame, text="Démarrer l'Acquisition (ou F10)", command=start_acquisition_and_plot, font='Helvetica 12 bold', pady=5).grid(row=row_idx, column=0, columnspan=2, pady=10)


    # --- CADRE DU GRAPHIQUE (DROITE) ---
    plot_frame_container = tk.Frame(main_frame, bd=2, relief=tk.SUNKEN)
    plot_frame_container.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=10, pady=10)

    create_initial_plot_notebook(plot_frame_container)
    
    try:
        root.state('zoomed') 
    except tk.TclError:
        root.attributes('-zoomed', True)

    root.mainloop()

if __name__ == "__main__":
    setup_main_window()