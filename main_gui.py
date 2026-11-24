
import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext, filedialog
from collections import defaultdict, deque
from typing import Set, Dict, List, FrozenSet
import webbrowser

class AFN_E:
    def __init__(self):
        self.estados: Set[str] = set()
        self.alfabeto: Set[str] = set()
        self.epsilon = 'e'
        self.inicial: str = ""
        self.finales: Set[str] = set()
        self.delta: Dict[str, Dict[str, Set[str]]] = defaultdict(lambda: defaultdict(set))

    def agregar_transicion(self, origen: str, simbolo: str, destinos: List[str]):
        for d in destinos:
            d = d.strip()
            if d:
                self.delta[origen][simbolo].add(d)


def cerradura_epsilon(estado, delta, epsilon):
    clausura = set()
    pila = [estado]
    while pila:
        actual = pila.pop()
        if actual not in clausura:
            clausura.add(actual)
            for destino in delta.get(actual, {}).get(epsilon, set()):
                if destino not in clausura:
                    pila.append(destino)
    return clausura


def cerradura_epsilon_conjunto(estados, delta, epsilon):
    resultado = set()
    for e in estados:
        resultado |= cerradura_epsilon(e, delta, epsilon)
    return resultado


def eliminar_epsilon(afn):
    clausuras = {q: cerradura_epsilon(q, afn.delta, afn.epsilon) for q in afn.estados}
    nuevo_delta = defaultdict(lambda: defaultdict(set))
    for q in afn.estados:
        for simbolo in afn.alfabeto:
            movidos = set()
            for p in clausuras[q]:
                movidos |= afn.delta[p].get(simbolo, set())
            if movidos:
                nuevo_delta[q][simbolo] = cerradura_epsilon_conjunto(movidos, afn.delta, afn.epsilon)
    nuevos_finales = {q for q in afn.estados if clausuras[q] & afn.finales}
    return nuevo_delta, afn.inicial, nuevos_finales, clausuras


def determinizar(alfabeto, delta_afn, inicial_afn, finales_afn, epsilon, clausuras):
    inicial_afd = frozenset(clausuras[inicial_afn])
    pendientes = deque([inicial_afd])
    visitados = {inicial_afd}
    delta_afd = {}
    estados_afd = []
    mapeo = {}

    def nombre(s):
        if s not in mapeo:
            mapeo[s] = "∅" if not s else "{" + ",".join(sorted(s)) + "}"
        return mapeo[s]

    while pendientes:
        actual = pendientes.popleft()
        estados_afd.append(actual)
        delta_afd[actual] = {}
        for simbolo in sorted(alfabeto):
            movidos = set()
            for p in actual:
                movidos |= delta_afn.get(p, {}).get(simbolo, set())
            nuevo = frozenset(cerradura_epsilon_conjunto(movidos, delta_afn, epsilon)) if movidos else frozenset()
            delta_afd[actual][simbolo] = nuevo
            if nuevo not in visitados:
                visitados.add(nuevo)
                if nuevo:
                    pendientes.append(nuevo)

    for s in list(estados_afd):
        for sim in alfabeto:
            dest = delta_afd[s].get(sim, frozenset())
            if not dest and dest not in estados_afd:
                estados_afd.append(dest)
                delta_afd[dest] = {sim: frozenset() for sim in alfabeto}

    finales_afd = {s for s in estados_afd if s & finales_afn}
    return estados_afd, delta_afd, inicial_afd, finales_afd, nombre


def generar_dot(estados_afd, delta_afd, inicial_afd, finales_afd, nombre_func, alfabeto):
    lineas = [
        "digraph AFD {",
        "    rankdir=LR;",
        "    size=\"11,8\";",
        "    bgcolor=\"white\";",
        "    node [shape=circle, fontsize=13, fontname=\"Arial\", style=filled, fillcolor=\"#e3f2fd\", color=\"#1565c0\"];",
        "    edge [fontsize=12, fontname=\"Arial\", color=\"#37474f\"];",
        "",
        "    inicio [shape=point, width=0.15, color=\"#00c853\"];",
        f"    inicio -> \"{nombre_func(inicial_afd)}\" [color=\"#00c853\", penwidth=2.0];",
        ""
    ]
    for s in estados_afd:
        nom = nombre_func(s)
        if s in finales_afd:
            lineas.append(f'    "{nom}" [shape=doublecircle, style=filled, fillcolor="#c8e6c9", color="#2e7d32", penwidth=2.0];')
        elif not s:
            lineas.append(f'    "{nom}" [style=filled, fillcolor="#ffcdd2", color="#c62828"];')
        else:
            lineas.append(f'    "{nom}";')
    lineas.append("")
    for origen in estados_afd:
        for simbolo in sorted(alfabeto):
            destino = delta_afd[origen].get(simbolo, frozenset())
            lineas.append(f'    "{nombre_func(origen)}" -> "{nombre_func(destino)}" [label=" {simbolo} "];')
    lineas.append("}")
    return "\n".join(lineas)

class Aplicacion(tk.Tk):
    PRIMARY       = "#1565C0"
    PRIMARY_DARK  = "#0D47A1"
    ACCENT        = "#00C853"
    BG            = "#ECEFF1"
    SURFACE       = "#FFFFFF"
    TEXT_PRIMARY  = "#212121"
    TEXT_SECONDARY= "#757575"
    DIVIDER       = "#B0BEC5"

    def __init__(self):
        super().__init__()
        self.title("AFN-ε → AFD")
        self.geometry("1200x800")
        self.minsize(1050, 720)
        self.configure(bg=self.BG)

        self.delta_afd = self.inicial_afd = self.finales_afd = None
        self.nombre_func = self.alfabeto = None

        self._estilos()
        self._ui()

    def _estilos(self):
        style = ttk.Style()
        style.theme_use("clam")
        style.configure(".", font=("Segoe UI", 10))
        style.configure("TFrame", background=self.BG)
        style.configure("TLabel", background=self.BG, foreground=self.TEXT_PRIMARY)

        style.configure("Primary.TButton", font=("Segoe UI", 11, "bold"), padding=(18, 10),
                        background=self.PRIMARY, foreground="white", borderwidth=0)
        style.map("Primary.TButton",
                  background=[("active", self.PRIMARY_DARK)], foreground=[("active", "white")])

        style.configure("Accent.TButton", font=("Segoe UI", 10, "bold"), padding=(14, 8),
                        background=self.ACCENT, foreground="white", borderwidth=0)
        style.map("Accent.TButton", background=[("active", "#00A043")])

        style.configure("Secondary.TButton", font=("Segoe UI", 10), padding=(12, 7),
                        background="#CFD8DC", foreground=self.TEXT_PRIMARY, borderwidth=0)
        style.map("Secondary.TButton", background=[("active", "#B0BEC5")])

        style.configure("Example.TButton", font=("Segoe UI", 10), padding=(12, 9),
                        background="#E3F2FD", foreground=self.PRIMARY, borderwidth=0)
        style.map("Example.TButton", background=[("active", "#BBDEFB")])

        style.configure("TEntry", font=("Segoe UI", 10), padding=7)
        style.configure("TNotebook", background=self.BG, borderwidth=0)
        style.configure("TNotebook.Tab", font=("Segoe UI", 10, "bold"), padding=(16, 9),
                        background="#CFD8DC", foreground=self.TEXT_SECONDARY)
        style.map("TNotebook.Tab",
                  background=[("selected", self.SURFACE)],
                  foreground=[("selected", self.PRIMARY)])

        style.configure("Tabla.Treeview",
                        font=("Segoe UI", 10),
                        rowheight=28,
                        background="white",
                        fieldbackground="white",
                        foreground=self.TEXT_PRIMARY,
                        borderwidth=0)
        style.configure("Tabla.Treeview.Heading",
                        font=("Segoe UI", 10, "bold"),
                        background=self.PRIMARY,
                        foreground="white",
                        relief="flat",
                        padding=6)
        style.map("Tabla.Treeview.Heading",
                  background=[("active", self.PRIMARY_DARK)])
        style.map("Tabla.Treeview",
                  background=[("selected", "#BBDEFB")],
                  foreground=[("selected", self.TEXT_PRIMARY)])

    def _tarjeta(self, parent):
        outer = tk.Frame(parent, bg="#CFD8DC", padx=1, pady=1)
        inner = tk.Frame(outer, bg=self.SURFACE)
        inner.pack(fill="both", expand=True)
        return outer, inner

    def _crear_tree(self, parent, columnas):
        """Crea un Treeview con scroll y estilo de tabla"""
        frame = tk.Frame(parent, bg=self.SURFACE)
        tree = ttk.Treeview(frame, columns=columnas, show="headings", style="Tabla.Treeview", height=6)

        for col in columnas:
            tree.heading(col, text=col)
            tree.column(col, anchor="center", width=100, minwidth=70)

        if columnas:
            tree.column(columnas[0], anchor="w", width=140, minwidth=100)

        vsb = ttk.Scrollbar(frame, orient="vertical", command=tree.yview)
        hsb = ttk.Scrollbar(frame, orient="horizontal", command=tree.xview)
        tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)

        tree.grid(row=0, column=0, sticky="nsew")
        vsb.grid(row=0, column=1, sticky="ns")
        hsb.grid(row=1, column=0, sticky="ew")
        frame.grid_rowconfigure(0, weight=1)
        frame.grid_columnconfigure(0, weight=1)

        # Filas alternadas
        tree.tag_configure("odd", background="#F5F9FC")
        tree.tag_configure("even", background="white")
        tree.tag_configure("inicial", background="#E8F5E9")
        tree.tag_configure("final", background="#FFF8E1")

        return frame, tree

    def _llenar_tree(self, tree, estados, alfabeto, delta, inicial, finales, es_afd=False):
        tree.delete(*tree.get_children())
        for i, q in enumerate(estados):
            marca = ""
            if q == inicial:
                marca += "→ "
            if q in finales:
                marca += "★ "
            valores = [f"{marca}{q}"]
            for s in alfabeto:
                dest = delta.get(q, {}).get(s, set())
                if not dest:
                    txt = "∅" if es_afd else "—"
                else:
                    txt = ",".join(sorted(dest))
                valores.append(txt)

            tags = []
            if q == inicial:
                tags.append("inicial")
            elif q in finales:
                tags.append("final")
            else:
                tags.append("odd" if i % 2 else "even")
            tree.insert("", "end", values=valores, tags=tags)

    def _ui(self):
        # APP BAR
        appbar = tk.Frame(self, bg=self.PRIMARY, height=56)
        appbar.pack(fill="x")
        appbar.pack_propagate(False)
        tk.Label(appbar, text="  AFN-ε  →  AFD", bg=self.PRIMARY, fg="white",
                 font=("Segoe UI", 15, "bold")).pack(side="left", padx=10, pady=12)
        tk.Label(appbar, text="Lenguajes Formales y Autómatas", bg=self.PRIMARY, fg="#BBDEFB",
                 font=("Segoe UI", 10)).pack(side="left", pady=16)

        body = tk.Frame(self, bg=self.BG)
        body.pack(fill="both", expand=True, padx=12, pady=10)

        # ===== IZQUIERDA =====
        izq = tk.Frame(body, bg=self.BG, width=340)
        izq.pack(side="left", fill="y", padx=(0, 10))
        izq.pack_propagate(False)

        out, card = self._tarjeta(izq)
        out.pack(fill="x", pady=(0, 8))
        tk.Label(card, text="  EJEMPLOS", bg=self.SURFACE, fg=self.PRIMARY,
                 font=("Segoe UI", 9, "bold")).pack(anchor="w", padx=10, pady=(8, 4))
        for i, txt in [(1, "Termina en abb"), (2, "Varias ε"), (3, "Alfabeto {0,1}")]:
            ttk.Button(card, text=f"  Ejemplo {i}  ·  {txt}", style="Example.TButton",
                       command=lambda n=i: self._cargar(n)).pack(fill="x", padx=8, pady=2)
        tk.Frame(card, bg=self.SURFACE, height=6).pack()

        out, card = self._tarjeta(izq)
        out.pack(fill="x", pady=(0, 8))
        tk.Label(card, text="  DATOS DEL AUTÓMATA", bg=self.SURFACE, fg=self.PRIMARY,
                 font=("Segoe UI", 9, "bold")).pack(anchor="w", padx=10, pady=(8, 4))

        def campo(parent, label, default=""):
            tk.Label(parent, text=label, bg=self.SURFACE, fg=self.TEXT_SECONDARY,
                     font=("Segoe UI", 8)).pack(anchor="w", padx=12)
            e = ttk.Entry(parent)
            e.pack(fill="x", padx=10, pady=(1, 5))
            e.insert(0, default)
            return e

        self.e_estados  = campo(card, "Estados", "q0 q1 q2 q3")
        self.e_alfabeto = campo(card, "Alfabeto (sin e)", "a b")
        self.e_inicial  = campo(card, "Estado inicial", "q0")
        self.e_finales  = campo(card, "Estados finales", "q3")
        tk.Frame(card, bg=self.SURFACE, height=4).pack()

        out, card = self._tarjeta(izq)
        out.pack(fill="x", pady=(0, 8))
        tk.Label(card, text="  TRANSICIONES", bg=self.SURFACE, fg=self.PRIMARY,
                 font=("Segoe UI", 9, "bold")).pack(anchor="w", padx=10, pady=(8, 2))
        tk.Label(card, text="  origen  símbolo  dest1,dest2", bg=self.SURFACE, fg=self.TEXT_SECONDARY,
                 font=("Segoe UI", 8)).pack(anchor="w", padx=10)
        self.txt_trans = scrolledtext.ScrolledText(card, height=4, font=("Consolas", 10),
                                                   relief="flat", bg="#F5F7FA",
                                                   highlightthickness=1, highlightbackground=self.DIVIDER)
        self.txt_trans.pack(fill="x", padx=8, pady=(4, 8))
        self.txt_trans.insert("1.0", "q0 e q1\nq1 a q1\nq1 b q1,q2\nq2 b q3\nq3 e q1")

        # Botones
        bf = tk.Frame(izq, bg=self.BG)
        bf.pack(fill="x", pady=(2, 0))
        tk.Button(bf, text="▶  CONVERTIR", font=("Segoe UI", 12, "bold"),
                  bg=self.PRIMARY, fg="white", activebackground=self.PRIMARY_DARK,
                  activeforeground="white", relief="flat", cursor="hand2",
                  padx=16, pady=9, command=self._convertir).pack(side="left", fill="x", expand=True, padx=(0, 6))
        tk.Button(bf, text="Limpiar", font=("Segoe UI", 10),
                  bg="#CFD8DC", fg=self.TEXT_PRIMARY, relief="flat", cursor="hand2",
                  padx=12, pady=9, command=self._limpiar).pack(side="left")

        der = tk.Frame(body, bg=self.BG)
        der.pack(side="left", fill="both", expand=True)

        self.nb = ttk.Notebook(der)
        self.nb.pack(fill="both", expand=True)

        # --- Tab Tablas (con tablas reales) ---
        t1 = tk.Frame(self.nb, bg=self.SURFACE)
        self.nb.add(t1, text="  Tablas  ")

    
        canvas = tk.Canvas(t1, bg=self.SURFACE, highlightthickness=0)
        scroll = ttk.Scrollbar(t1, orient="vertical", command=canvas.yview)
        self.frame_tablas = tk.Frame(canvas, bg=self.SURFACE)

        self.frame_tablas.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=self.frame_tablas, anchor="nw")
        canvas.configure(yscrollcommand=scroll.set)

        canvas.pack(side="left", fill="both", expand=True)
        scroll.pack(side="right", fill="y")

        # Bind mousewheel
        def _on_mousewheel(event):
            canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
        canvas.bind_all("<MouseWheel>", _on_mousewheel)

      
        self.lbl_info = tk.Label(self.frame_tablas, text="Presiona CONVERTIR para ver las tablas",
                                 bg=self.SURFACE, fg=self.TEXT_SECONDARY, font=("Segoe UI", 11))
        self.lbl_info.pack(pady=20)

  
        self.trees = {}

 
        t2 = tk.Frame(self.nb, bg=self.SURFACE)
        self.nb.add(t2, text="  Validar cadenas  ")
        top = tk.Frame(t2, bg=self.SURFACE)
        top.pack(fill="x", padx=16, pady=12)
        tk.Label(top, text="Cadena:", bg=self.SURFACE, fg=self.TEXT_SECONDARY,
                 font=("Segoe UI", 9)).pack(side="left")
        self.e_cadena = ttk.Entry(top, width=24)
        self.e_cadena.pack(side="left", padx=8)
        tk.Button(top, text="PROBAR", font=("Segoe UI", 10, "bold"),
                  bg=self.ACCENT, fg="white", activebackground="#00A043",
                  relief="flat", cursor="hand2", padx=14, pady=5,
                  command=self._probar).pack(side="left")
        self.txt_val = scrolledtext.ScrolledText(t2, font=("Consolas", 11), relief="flat",
                                                 bg="#FAFBFC", padx=12, pady=12)
        self.txt_val.pack(fill="both", expand=True, padx=8, pady=(0, 8))

      
        t3 = tk.Frame(self.nb, bg=self.SURFACE)
        self.nb.add(t3, text="  Diagrama  ")
        top3 = tk.Frame(t3, bg=self.SURFACE)
        top3.pack(fill="x", padx=16, pady=12)
        tk.Button(top3, text="Guardar .dot", font=("Segoe UI", 10),
                  bg="#CFD8DC", fg=self.TEXT_PRIMARY, relief="flat", cursor="hand2",
                  padx=12, pady=5, command=self._guardar_dot).pack(side="left", padx=(0, 8))
        tk.Button(top3, text="Abrir Graphviz Online", font=("Segoe UI", 10, "bold"),
                  bg=self.PRIMARY, fg="white", activebackground=self.PRIMARY_DARK,
                  relief="flat", cursor="hand2", padx=14, pady=5,
                  command=self._abrir_online).pack(side="left")
        self.txt_dot = scrolledtext.ScrolledText(t3, font=("Consolas", 9), relief="flat",
                                                 bg="#FAFBFC", padx=12, pady=12)
        self.txt_dot.pack(fill="both", expand=True, padx=8, pady=(0, 8))

        self.status = tk.Label(self, text="  Listo · Elige un ejemplo y pulsa CONVERTIR",
                               bg=self.PRIMARY_DARK, fg="#BBDEFB",
                               font=("Segoe UI", 9), anchor="w", padx=12, pady=6)
        self.status.pack(fill="x", side="bottom")

    def _status(self, msg):
        self.status.config(text=f"  {msg}")

    def _cargar(self, n):
        data = {
            1: ("q0 q1 q2 q3", "a b", "q0", "q3",
                "q0 e q1\nq1 a q1\nq1 b q1,q2\nq2 b q3\nq3 e q1"),
            2: ("q0 q1 q2 q3 q4", "a b", "q0", "q4",
                "q0 e q1,q2\nq1 a q3\nq2 b q3\nq3 e q4\nq4 a q4\nq4 b q4"),
            3: ("q0 q1 q2", "0 1", "q0", "q2",
                "q0 e q1\nq1 0 q1\nq1 1 q2\nq2 e q0"),
        }
        e, a, i, f, t = data[n]
        for w, val in [(self.e_estados, e), (self.e_alfabeto, a),
                       (self.e_inicial, i), (self.e_finales, f)]:
            w.delete(0, "end")
            w.insert(0, val)
        self.txt_trans.delete("1.0", "end")
        self.txt_trans.insert("1.0", t)
        self._status(f"Ejemplo {n} cargado · Presiona CONVERTIR")

    def _limpiar(self):
        for w in (self.e_estados, self.e_alfabeto, self.e_inicial, self.e_finales):
            w.delete(0, "end")
        self.txt_trans.delete("1.0", "end")
        self.txt_val.delete("1.0", "end")
        self.txt_dot.delete("1.0", "end")
        for w in self.frame_tablas.winfo_children():
            w.destroy()
        self.lbl_info = tk.Label(self.frame_tablas, text="Presiona CONVERTIR para ver las tablas",
                                 bg=self.SURFACE, fg=self.TEXT_SECONDARY, font=("Segoe UI", 11))
        self.lbl_info.pack(pady=20)
        self.delta_afd = None
        self._status("Campos limpiados")

    def _build_afn(self):
        afn = AFN_E()
        estados = self.e_estados.get().strip().split()
        if len(estados) < 2:
            raise ValueError("Necesitas al menos 2 estados.")
        afn.estados = set(estados)
        alfabeto = self.e_alfabeto.get().strip().split()
        if not (1 <= len(alfabeto) <= 4) or "e" in alfabeto:
            raise ValueError("Alfabeto: 1–4 símbolos, sin usar 'e'.")
        afn.alfabeto = set(alfabeto)
        inicial = self.e_inicial.get().strip()
        if inicial not in afn.estados:
            raise ValueError(f"Inicial '{inicial}' no está en los estados.")
        afn.inicial = inicial
        finales = self.e_finales.get().strip().split()
        if not finales or any(f not in afn.estados for f in finales):
            raise ValueError("Revisa los estados finales.")
        afn.finales = set(finales)
        for linea in self.txt_trans.get("1.0", "end").strip().splitlines():
            p = linea.strip().split()
            if len(p) < 2:
                continue
            origen, sim = p[0], p[1]
            dests = p[2].split(",") if len(p) > 2 else []
            if origen not in afn.estados:
                raise ValueError(f"Origen '{origen}' no existe.")
            afn.agregar_transicion(origen, sim, dests)
        return afn

    def _seccion_tabla(self, parent, titulo, info=""):
        """Crea una sección con título + treeview"""
        frm = tk.Frame(parent, bg=self.SURFACE)
        frm.pack(fill="x", padx=12, pady=(12, 4))
        tk.Label(frm, text=titulo, bg=self.SURFACE, fg=self.PRIMARY,
                 font=("Segoe UI", 11, "bold")).pack(anchor="w")
        if info:
            tk.Label(frm, text=info, bg=self.SURFACE, fg=self.TEXT_SECONDARY,
                     font=("Segoe UI", 9)).pack(anchor="w")
        return frm

    def _convertir(self):
        try:
            afn = self._build_afn()
        except ValueError as e:
            messagebox.showerror("Datos incorrectos", str(e))
            return

        self._status("Procesando…")

        
        for w in self.frame_tablas.winfo_children():
            w.destroy()

        estados = sorted(afn.estados)
        alf = sorted(afn.alfabeto)
        alf_e = alf + [afn.epsilon]

     
        self._seccion_tabla(self.frame_tablas, "1. Tabla del AFN-ε original",
                            f"Inicial: {afn.inicial}   |   Finales: {', '.join(sorted(afn.finales))}")
        cols1 = ["Estado"] + alf_e
        f1, t1 = self._crear_tree(self.frame_tablas, cols1)
        f1.pack(fill="x", padx=12, pady=(0, 8))
        self._llenar_tree(t1, estados, alf_e, afn.delta, afn.inicial, afn.finales)

        delta_afn, ini_afn, fin_afn, clausuras = eliminar_epsilon(afn)
        sec = self._seccion_tabla(self.frame_tablas, "2. ε-clausuras")
        txt_c = tk.Text(self.frame_tablas, height=len(estados)+1, font=("Consolas", 10),
                        relief="flat", bg="#F5F9FC", padx=10, pady=6)
        txt_c.pack(fill="x", padx=12, pady=(0, 8))
        for q in estados:
            txt_c.insert("end", f"  ε-clausura({q})  =  {{{', '.join(sorted(clausuras[q]))}}}\n")
        txt_c.config(state="disabled")

     
        self._seccion_tabla(self.frame_tablas, "3. Tabla del AFN (sin ε)",
                            f"Inicial: {ini_afn}   |   Finales: {', '.join(sorted(fin_afn))}")
        cols3 = ["Estado"] + alf
        f3, t3 = self._crear_tree(self.frame_tablas, cols3)
        f3.pack(fill="x", padx=12, pady=(0, 8))
        self._llenar_tree(t3, estados, alf, delta_afn, ini_afn, fin_afn)

   
        ea, da, ia, fa, nombre = determinizar(
            afn.alfabeto, delta_afn, afn.inicial, afn.finales, afn.epsilon, clausuras)

        self.delta_afd, self.inicial_afd, self.finales_afd = da, ia, fa
        self.nombre_func, self.alfabeto = nombre, afn.alfabeto

        noms = [nombre(s) for s in ea]
        dp = {}
        for s in ea:
            dp[nombre(s)] = {sim: nombre(da[s].get(sim, frozenset())) for sim in afn.alfabeto}

        self._seccion_tabla(self.frame_tablas, "4. Tabla del AFD final",
                            f"Inicial: {nombre(ia)}   |   Finales: {', '.join(sorted(nombre(f) for f in fa))}")
        cols4 = ["Estado"] + alf
        f4, t4 = self._crear_tree(self.frame_tablas, cols4)
        f4.pack(fill="x", padx=12, pady=(0, 16))
        self._llenar_tree(t4, noms, alf, dp, nombre(ia), {nombre(f) for f in fa}, es_afd=True)

    
        ley = tk.Label(self.frame_tablas,
                       text="  →  = estado inicial     ★  = estado de aceptación     ∅  = conjunto vacío",
                       bg=self.SURFACE, fg=self.TEXT_SECONDARY, font=("Segoe UI", 9))
        ley.pack(anchor="w", padx=12, pady=(0, 20))

        self.nb.select(0)
        self.txt_dot.delete("1.0", "end")
        self.txt_dot.insert("1.0", generar_dot(ea, da, ia, fa, nombre, afn.alfabeto))
        self._status("✓ Conversión lista · Revisa las tablas")

    def _probar(self):
        if self.delta_afd is None:
            messagebox.showinfo("Atención", "Primero convierte el autómata.")
            return
        cadena = self.e_cadena.get().strip()
        if not cadena:
            return
        actual = self.inicial_afd
        rec = [self.nombre_func(actual)]
        msg = ""
        for s in cadena:
            if s not in self.alfabeto:
                msg = f"  Símbolo '{s}' fuera del alfabeto\n  → RECHAZADA"
                break
            if s not in self.delta_afd.get(actual, {}):
                msg = f"  Sin transición con '{s}'\n  → RECHAZADA"
                break
            actual = self.delta_afd[actual][s]
            rec.append(self.nombre_func(actual))
        else:
            ok = actual in self.finales_afd
            msg = f"  Recorrido: {' → '.join(rec)}\n  → {'ACEPTADA ✓' if ok else 'RECHAZADA'}"
        self.txt_val.insert("end", f"Cadena \"{cadena}\"\n{msg}\n\n")
        self.txt_val.see("end")
        self.nb.select(1)

    def _guardar_dot(self):
        if self.delta_afd is None:
            messagebox.showinfo("Atención", "Primero convierte el autómata.")
            return
        ruta = filedialog.asksaveasfilename(defaultextension=".dot",
                                            filetypes=[("Graphviz DOT", "*.dot")])
        if ruta:
            with open(ruta, "w", encoding="utf-8") as f:
                f.write(self.txt_dot.get("1.0", "end").strip())
            self._status(f"Guardado: {ruta}")

    def _abrir_online(self):
        webbrowser.open("https://dreampuf.github.io/GraphvizOnline/")
        self._status("Copia el código DOT y pégalo en Graphviz Online")


if __name__ == "__main__":
    app = Aplicacion()
    app.mainloop()
