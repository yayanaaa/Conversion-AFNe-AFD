

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
        "    node [shape=circle, fontsize=13, fontname=\"Arial\", style=filled, fillcolor=\"#e8f4fd\", color=\"#2c3e50\"];",
        "    edge [fontsize=12, fontname=\"Arial\", color=\"#34495e\"];",
        "",
        "    inicio [shape=point, width=0.15, color=\"#27ae60\"];",
        f"    inicio -> \"{nombre_func(inicial_afd)}\" [color=\"#27ae60\", penwidth=2.0];",
        ""
    ]
    for s in estados_afd:
        nom = nombre_func(s)
        if s in finales_afd:
            lineas.append(f'    "{nom}" [shape=doublecircle, style=filled, fillcolor="#d4edda", color="#28a745", penwidth=2.0];')
        elif not s:
            lineas.append(f'    "{nom}" [style=filled, fillcolor="#f8d7da", color="#dc3545"];')
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
    BG = "#f4f6f9"
    CARD = "#ffffff"
    PRIMARY = "#2563eb"
    PRIMARY_HOVER = "#1d4ed8"
    SUCCESS = "#16a34a"
    TEXT = "#1e293b"
    MUTED = "#64748b"
    BORDER = "#e2e8f0"

    def __init__(self):
        super().__init__()
        self.title("Conversión AFN-ε → AFD")
        self.geometry("1150x750")
        self.minsize(1000, 680)
        self.configure(bg=self.BG)

        self.afn = None
        self.estados_afd = self.delta_afd = self.inicial_afd = None
        self.finales_afd = self.nombre_func = self.alfabeto = None

        self._configurar_estilos()
        self._construir_ui()

    def _configurar_estilos(self):
        style = ttk.Style()
        style.theme_use("clam")

        style.configure(".", background=self.BG, foreground=self.TEXT, font=("Segoe UI", 10))
        style.configure("TFrame", background=self.BG)
        style.configure("Card.TFrame", background=self.CARD)
        style.configure("TLabel", background=self.BG, foreground=self.TEXT, font=("Segoe UI", 10))
        style.configure("Card.TLabel", background=self.CARD, foreground=self.TEXT, font=("Segoe UI", 10))
        style.configure("Titulo.TLabel", background=self.BG, foreground=self.TEXT, font=("Segoe UI", 18, "bold"))
        style.configure("Sub.TLabel", background=self.BG, foreground=self.MUTED, font=("Segoe UI", 10))

        style.configure("TButton", font=("Segoe UI", 10), padding=(12, 6), background=self.CARD, foreground=self.TEXT)
        style.map("TButton", background=[("active", self.BORDER)])

        style.configure("Primary.TButton", font=("Segoe UI", 10, "bold"), padding=(14, 8),
                        background=self.PRIMARY, foreground="white")
        style.map("Primary.TButton",
                  background=[("active", self.PRIMARY_HOVER), ("pressed", self.PRIMARY_HOVER)],
                  foreground=[("active", "white")])

        style.configure("Success.TButton", font=("Segoe UI", 10), padding=(12, 6),
                        background=self.SUCCESS, foreground="white")
        style.map("Success.TButton", background=[("active", "#15803d")])

        style.configure("TEntry", font=("Segoe UI", 10), padding=6)
        style.configure("TNotebook", background=self.BG, borderwidth=0)
        style.configure("TNotebook.Tab", font=("Segoe UI", 10), padding=(16, 8), background=self.BORDER)
        style.map("TNotebook.Tab", background=[("selected", self.CARD)], foreground=[("selected", self.PRIMARY)])

        style.configure("Status.TLabel", background="#e2e8f0", foreground=self.MUTED, font=("Segoe UI", 9), padding=6)

    def _card(self, parent, **kwargs):
        f = tk.Frame(parent, bg=self.CARD, highlightbackground=self.BORDER,
                     highlightthickness=1, **kwargs)
        return f

    def _construir_ui(self):
        header = tk.Frame(self, bg=self.BG)
        header.pack(fill="x", padx=20, pady=(16, 8))
        ttk.Label(header, text="Conversión AFN-ε → AFD", style="Titulo.TLabel").pack(side="left")
        ttk.Label(header, text="  Lenguajes Formales y Autómatas", style="Sub.TLabel").pack(side="left", pady=6)

        body = tk.Frame(self, bg=self.BG)
        body.pack(fill="both", expand=True, padx=20, pady=8)

        izq = tk.Frame(body, bg=self.BG, width=340)
        izq.pack(side="left", fill="y", padx=(0, 12))
        izq.pack_propagate(False)

        
        card_ej = self._card(izq)
        card_ej.pack(fill="x", pady=(0, 10))
        tk.Label(card_ej, text="EJEMPLOS RÁPIDOS", bg=self.CARD, fg=self.MUTED,
                 font=("Segoe UI", 8, "bold")).pack(anchor="w", padx=14, pady=(12, 6))
        for i, txt in [(1, "Termina en  abb"), (2, "Varias transiciones ε"), (3, "Alfabeto {0, 1}")]:
            b = ttk.Button(card_ej, text=f"  Ejemplo {i}:  {txt}", command=lambda n=i: self._cargar_ejemplo(n))
            b.pack(fill="x", padx=12, pady=3)
        tk.Frame(card_ej, bg=self.CARD, height=8).pack()

        card_datos = self._card(izq)
        card_datos.pack(fill="x", pady=(0, 10))
        tk.Label(card_datos, text="DATOS DEL AUTÓMATA", bg=self.CARD, fg=self.MUTED,
                 font=("Segoe UI", 8, "bold")).pack(anchor="w", padx=14, pady=(12, 8))

        def campo(parent, label, default=""):
            tk.Label(parent, text=label, bg=self.CARD, fg=self.TEXT, font=("Segoe UI", 9)).pack(anchor="w", padx=14)
            e = ttk.Entry(parent)
            e.pack(fill="x", padx=14, pady=(2, 8))
            e.insert(0, default)
            return e

        self.entry_estados = campo(card_datos, "Estados (separados por espacio)", "q0 q1 q2 q3")
        self.entry_alfabeto = campo(card_datos, "Alfabeto (máx 4, sin 'e')", "a b")
        self.entry_inicial = campo(card_datos, "Estado inicial", "q0")
        self.entry_finales = campo(card_datos, "Estados finales", "q3")
        tk.Frame(card_datos, bg=self.CARD, height=4).pack()

      
        card_trans = self._card(izq)
        card_trans.pack(fill="both", expand=True, pady=(0, 10))
        tk.Label(card_trans, text="TRANSICIONES", bg=self.CARD, fg=self.MUTED,
                 font=("Segoe UI", 8, "bold")).pack(anchor="w", padx=14, pady=(12, 2))
        tk.Label(card_trans, text="formato:  origen  símbolo  dest1,dest2", bg=self.CARD, fg=self.MUTED,
                 font=("Segoe UI", 8)).pack(anchor="w", padx=14, pady=(0, 6))
        self.txt_trans = scrolledtext.ScrolledText(card_trans, height=7, font=("Consolas", 10),
                                                   relief="flat", bd=0, highlightthickness=1,
                                                   highlightbackground=self.BORDER)
        self.txt_trans.pack(fill="both", expand=True, padx=12, pady=(0, 12))
        self.txt_trans.insert("1.0", "q0 e q1\nq1 a q1\nq1 b q1,q2\nq2 b q3\nq3 e q1")

       
        frame_btn = tk.Frame(izq, bg=self.BG)
        frame_btn.pack(fill="x", pady=(4, 0))
        ttk.Button(frame_btn, text="▶  Convertir", style="Primary.TButton",
                   command=self._convertir).pack(side="left", padx=(0, 8))
        ttk.Button(frame_btn, text="Limpiar", command=self._limpiar).pack(side="left")

       
        der = tk.Frame(body, bg=self.BG)
        der.pack(side="left", fill="both", expand=True)

        self.notebook = ttk.Notebook(der)
        self.notebook.pack(fill="both", expand=True)

        tab1 = tk.Frame(self.notebook, bg=self.CARD)
        self.notebook.add(tab1, text="  Tablas  ")
        self.txt_tablas = scrolledtext.ScrolledText(tab1, font=("Consolas", 10), relief="flat",
                                                    bg="#fafbfc", padx=10, pady=10)
        self.txt_tablas.pack(fill="both", expand=True, padx=2, pady=2)

        tab2 = tk.Frame(self.notebook, bg=self.CARD)
        self.notebook.add(tab2, text="  Validar cadenas  ")
        top_val = tk.Frame(tab2, bg=self.CARD)
        top_val.pack(fill="x", padx=16, pady=14)
        tk.Label(top_val, text="Cadena:", bg=self.CARD, font=("Segoe UI", 10)).pack(side="left")
        self.entry_cadena = ttk.Entry(top_val, width=28)
        self.entry_cadena.pack(side="left", padx=8)
        ttk.Button(top_val, text="Probar", style="Success.TButton", command=self._probar).pack(side="left")
        self.txt_val = scrolledtext.ScrolledText(tab2, font=("Consolas", 11), relief="flat",
                                                 bg="#fafbfc", padx=10, pady=10)
        self.txt_val.pack(fill="both", expand=True, padx=12, pady=(0, 12))

        tab3 = tk.Frame(self.notebook, bg=self.CARD)
        self.notebook.add(tab3, text="  Diagrama  ")
        top_dot = tk.Frame(tab3, bg=self.CARD)
        top_dot.pack(fill="x", padx=16, pady=14)
        ttk.Button(top_dot, text="Guardar .dot", command=self._guardar_dot).pack(side="left", padx=(0, 8))
        ttk.Button(top_dot, text="Abrir Graphviz Online", style="Primary.TButton",
                   command=self._abrir_online).pack(side="left")
        self.txt_dot = scrolledtext.ScrolledText(tab3, font=("Consolas", 9), relief="flat",
                                                 bg="#fafbfc", padx=10, pady=10)
        self.txt_dot.pack(fill="both", expand=True, padx=12, pady=(0, 12))

        self.status = ttk.Label(self, text="  Listo. Elige un ejemplo o escribe tu AFN-ε y presiona Convertir.",
                                style="Status.TLabel")
        self.status.pack(fill="x", side="bottom")

    def _status(self, msg):
        self.status.config(text=f"  {msg}")

    def _cargar_ejemplo(self, n):
        data = {
            1: ("q0 q1 q2 q3", "a b", "q0", "q3", "q0 e q1\nq1 a q1\nq1 b q1,q2\nq2 b q3\nq3 e q1"),
            2: ("q0 q1 q2 q3 q4", "a b", "q0", "q4", "q0 e q1,q2\nq1 a q3\nq2 b q3\nq3 e q4\nq4 a q4\nq4 b q4"),
            3: ("q0 q1 q2", "0 1", "q0", "q2", "q0 e q1\nq1 0 q1\nq1 1 q2\nq2 e q0"),
        }
        e, a, i, f, t = data[n]
        for entry, val in [(self.entry_estados, e), (self.entry_alfabeto, a),
                           (self.entry_inicial, i), (self.entry_finales, f)]:
            entry.delete(0, "end")
            entry.insert(0, val)
        self.txt_trans.delete("1.0", "end")
        self.txt_trans.insert("1.0", t)
        self._status(f"Ejemplo {n} cargado. Presiona Convertir.")

    def _limpiar(self):
        for e in (self.entry_estados, self.entry_alfabeto, self.entry_inicial, self.entry_finales):
            e.delete(0, "end")
        self.txt_trans.delete("1.0", "end")
        self.txt_tablas.delete("1.0", "end")
        self.txt_val.delete("1.0", "end")
        self.txt_dot.delete("1.0", "end")
        self.delta_afd = None
        self._status("Campos limpiados.")

    def _construir_afn(self):
        afn = AFN_E()
        estados = self.entry_estados.get().strip().split()
        if len(estados) < 2:
            raise ValueError("Necesitas al menos 2 estados.")
        afn.estados = set(estados)

        alfabeto = self.entry_alfabeto.get().strip().split()
        if not (1 <= len(alfabeto) <= 4) or "e" in alfabeto:
            raise ValueError("Alfabeto: 1 a 4 símbolos, sin usar la letra 'e'.")
        afn.alfabeto = set(alfabeto)

        inicial = self.entry_inicial.get().strip()
        if inicial not in afn.estados:
            raise ValueError(f"El inicial '{inicial}' no está en los estados.")
        afn.inicial = inicial

        finales = self.entry_finales.get().strip().split()
        if not finales or any(f not in afn.estados for f in finales):
            raise ValueError("Revisa los estados finales.")
        afn.finales = set(finales)

        for linea in self.txt_trans.get("1.0", "end").strip().splitlines():
            partes = linea.strip().split()
            if len(partes) < 2:
                continue
            origen, simbolo = partes[0], partes[1]
            destinos = partes[2].split(",") if len(partes) > 2 else []
            if origen not in afn.estados:
                raise ValueError(f"Estado origen '{origen}' no existe.")
            afn.agregar_transicion(origen, simbolo, destinos)
        return afn

    def _fmt_tabla(self, titulo, estados, alfabeto, delta, inicial, finales, es_afd=False):
        L = ["=" * 68, f"  {titulo}", "=" * 68]
        header = f"{'Estado':<22}" + "".join(f"| {s:^11}" for s in alfabeto)
        L += [header, "-" * len(header)]
        for q in estados:
            marca = ""
            if q == inicial:
                marca += "→ "
            if q in finales:
                marca += "* "
            if not marca:
                marca = "  "
            fila = f"{marca}{q:<20}"
            for s in alfabeto:
                dest = delta.get(q, {}).get(s, set())
                texto = ("∅" if es_afd else "-") if not dest else ",".join(sorted(dest))
                fila += f"| {texto:^11}"
            L.append(fila)
        L += ["=" * 68,
              f"  Inicial : {inicial}",
              f"  Finales : {', '.join(sorted(finales)) or '(ninguno)'}",
              "  (→ inicial   * aceptación)", ""]
        return "\n".join(L)

    def _convertir(self):
        try:
            afn = self._construir_afn()
        except ValueError as e:
            messagebox.showerror("Datos incorrectos", str(e))
            return

        self.afn = afn
        self._status("Procesando...")

        estados = sorted(afn.estados)
        alf_e = sorted(afn.alfabeto) + [afn.epsilon]
        texto = self._fmt_tabla("1. AFN-ε ORIGINAL", estados, alf_e, afn.delta, afn.inicial, afn.finales)

        delta_afn, ini_afn, fin_afn, clausuras = eliminar_epsilon(afn)
        texto += "\n  ε-CLAUSURAS\n"
        for q in estados:
            texto += f"    ε-clausura({q}) = {{{', '.join(sorted(clausuras[q]))}}}\n"
        texto += "\n"

        alf = sorted(afn.alfabeto)
        texto += self._fmt_tabla("3. AFN (sin ε)", estados, alf, delta_afn, ini_afn, fin_afn)

        estados_afd, delta_afd, ini_afd, fin_afd, nombre = determinizar(
            afn.alfabeto, delta_afn, afn.inicial, afn.finales, afn.epsilon, clausuras)

        self.estados_afd, self.delta_afd = estados_afd, delta_afd
        self.inicial_afd, self.finales_afd = ini_afd, fin_afd
        self.nombre_func, self.alfabeto = nombre, afn.alfabeto

        noms = [nombre(s) for s in estados_afd]
        delta_p = {nombre(s): {sim: nombre(delta_afd[s].get(sim, frozenset())) for sim in afn.alfabeto}
                   for s in estados_afd}
        texto += self._fmt_tabla("4. AFD FINAL", noms, alf, delta_p, nombre(ini_afd),
                                 {nombre(f) for f in fin_afd}, es_afd=True)

        self.txt_tablas.delete("1.0", "end")
        self.txt_tablas.insert("1.0", texto)
        self.notebook.select(0)

        dot = generar_dot(estados_afd, delta_afd, ini_afd, fin_afd, nombre, afn.alfabeto)
        self.txt_dot.delete("1.0", "end")
        self.txt_dot.insert("1.0", dot)
        self._status("Conversión lista. Revisa las tablas o prueba cadenas.")

    def _probar(self):
        if self.delta_afd is None:
            messagebox.showinfo("Atención", "Primero convierte el autómata.")
            return
        cadena = self.entry_cadena.get().strip()
        if not cadena:
            return
        actual = self.inicial_afd
        rec = [self.nombre_func(actual)]
        msg = ""
        for s in cadena:
            if s not in self.alfabeto:
                msg = f"  Símbolo '{s}' no está en el alfabeto\n  → RECHAZADA"
                break
            if s not in self.delta_afd.get(actual, {}):
                msg = f"  Sin transición con '{s}'\n  → RECHAZADA"
                break
            actual = self.delta_afd[actual][s]
            rec.append(self.nombre_func(actual))
        else:
            ok = actual in self.finales_afd
            msg = f"  Recorrido: {' → '.join(rec)}\n  → {'ACEPTADA' if ok else 'RECHAZADA'}"
        self.txt_val.insert("end", f"Cadena \"{cadena}\"\n{msg}\n\n")
        self.txt_val.see("end")
        self.notebook.select(1)

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
        self._status("Copia el código DOT y pégalo en Graphviz Online.")


if __name__ == "__main__":
    app = Aplicacion()
    app.mainloop()
