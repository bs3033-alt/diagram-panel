import tkinter as tk
from tkinter import messagebox, filedialog, simpledialog, ttk, colorchooser
import json
import copy
import os
import tempfile
import re
import math
import time
import datetime
import webbrowser

# Попытка импорта PIL для работы с растровой графикой
try:
    from PIL import Image, ImageTk, ImageGrab, ImageSequence
    HAS_PIL = True
except ImportError:
    HAS_PIL = False

try:
    import winsound
    HAS_WINSOUND = True
except ImportError:
    HAS_WINSOUND = False

AUDIO_EXTENSIONS = (".wav", ".mp3", ".ogg", ".flac", ".wma", ".m4a", ".aac")

class DataRow:
    """Объект строки данных, позволяющий получать значения по атрибутам (регистронезависимо)."""
    def __init__(self, data_dict):
        self._data = data_dict
        self._lower_keys = {str(k).lower(): k for k in data_dict.keys()}
        
    def __getattr__(self, item):
        if item in self._data: 
            return self._data[item]
        lower_item = str(item).lower()
        if lower_item in self._lower_keys:
            return self._data[self._lower_keys[lower_item]]
        raise AttributeError(f"Row has no attribute '{item}'")
        
    def __getitem__(self, item):
        return self.__getattr__(item)
        
    def __repr__(self):
        return str(self._data)

class DataTable:
    """Объект таблицы сводки данных. Поддерживает обращения Table.Column и Table[index]."""
    def __init__(self, name, headers, rows_data):
        self.name = name
        self.headers = headers
        self.rows_data = rows_data
        self.rows = [DataRow(r) for r in rows_data]
        self.primary_key = headers[0] if headers else None

    def __eq__(self, other):
        if not isinstance(other, DataTable): 
            return False
        return self.name == other.name and self.rows_data == other.rows_data

    def __getattr__(self, item):
        if item in self.headers:
            return [r._data.get(item) for r in self.rows]
            
        lower_item = str(item).lower()
        for h in self.headers:
            if str(h).lower() == lower_item:
                return [r._data.get(h) for r in self.rows]

        if self.primary_key:
            for r in self.rows:
                val = r._data.get(self.primary_key)
                if str(val).lower() == lower_item or val == item:
                    return r
                    
        raise AttributeError(f"Table '{self.name}' has no column or row '{item}'")

    def __getitem__(self, key):
        if isinstance(key, int):
            if 0 <= key < len(self.rows):
                return self.rows[key]
            raise IndexError(f"Index {key} out of range for table '{self.name}'")
        return self.__getattr__(key)

    def __len__(self):
        return len(self.rows)

def split_csv_line(line):
    """Безопасное разбиение CSV-строки с игнорированием запятых внутри скобок."""
    parts, current = [], []
    depth = 0
    for char in line:
        if char in '({[': 
            depth += 1
        elif char in ')}]': 
            depth -= 1
        elif char == ',' and depth <= 0:
            parts.append(''.join(current).strip())
            current = []
            continue
        current.append(char)
    parts.append(''.join(current).strip())
    return parts

def _safe_sin(x): return round(math.sin(math.radians(x)), 10)
def _safe_cos(x): return round(math.cos(math.radians(x)), 10)
def _safe_tan(x):
    if x % 90 == 0 and (x / 90) % 2 != 0: 
        return float('inf')
    return round(math.tan(math.radians(x)), 10)
def _safe_asin(x): return round(math.degrees(math.asin(x)), 10)
def _safe_acos(x): return round(math.degrees(math.acos(x)), 10)
def _safe_atan(x): return round(math.degrees(math.atan(x)), 10)

SAFE_MATH_DICT = {k: getattr(math, k) for k in dir(math) if not k.startswith("_")}
SAFE_MATH_DICT.update({
    "sin": _safe_sin, "cos": _safe_cos, "tan": _safe_tan,
    "asin": _safe_asin, "acos": _safe_acos, "atan": _safe_atan,
    "sum": sum, "len": len, "max": max, "min": min
})

KW_BLUE = {"def", "class", "import", "from", "return", "if", "else", "elif", "for", "while", "True", "False", "None", "and", "or", "not", "pass", "try", "except"}

RE_MATH_SQRT = re.compile(r'√(\d+\.?\d*)')
RE_CODE_TOKENS = re.compile(r'".*?"|\'.*?\'|#.*|//.*|/\*.*?\*/|\b\w+\b|\s+|\S')
RE_HTML_STYLE_BLOCK = re.compile(r'<style[^>]*>(.*?)</style>', re.IGNORECASE | re.DOTALL)
RE_CSS_RULES = re.compile(r'([^{]+)\{([^}]+)\}')
RE_HTML_TAG = re.compile(r'<([a-zA-Z0-9]+)([^>]*)>')
RE_HTML_CLASS = re.compile(r'class=["\']([^"\']+)["\']', re.IGNORECASE)
RE_HTML_STYLE_ATTR = re.compile(r'style=["\']([^"\']+)["\']', re.IGNORECASE)
RE_STRIP_TAGS = re.compile(r'<[^>]+>')
RE_CHART_SPLIT = re.compile(r'[:|]')
RE_INTERPOLATION_BRACKETS = re.compile(r"\{([^}]+)\}")
RE_CHAIN_ACCESS = re.compile(r"\{([^}]+)\}((?:\[[^\]]+\]|\.[a-zA-Z0-9_]+)*)")

def evaluate_math_expression(expr, vars_dict=None):
    if not expr.strip():
        return None, False, ""

    context = vars_dict or {}
    math_expr = expr.replace('×', '*').replace('÷', '/').replace('^', '**')
    math_expr = math_expr.replace('²', '**2').replace('³', '**3')
    math_expr = math_expr.replace('√(', 'sqrt(')
    math_expr = RE_MATH_SQRT.sub(r'sqrt(\1)', math_expr)
    math_expr = math_expr.replace('π', 'pi').replace('∞', 'inf')
    math_expr = math_expr.replace('≠', '!=').replace('≤', '<=').replace('≥', '>=').replace('≈', '==')

    math_expr = RE_INTERPOLATION_BRACKETS.sub(r"(\1)", math_expr)
    is_comp = any(op in math_expr for op in ('==', '!=', '<=', '>=', '<', '>'))

    if '=' in math_expr and not is_comp:
        test_expr = math_expr.replace('=', '==')
        try:
            eval(test_expr, {"__builtins__": None}, {**SAFE_MATH_DICT, **context})
            math_expr = test_expr
            is_comp = True
        except Exception:
            parts = math_expr.split('=', 1)
            if len(parts) > 1:
                math_expr = parts[1].strip()

    try:
        res = eval(math_expr, {"__builtins__": None}, {**SAFE_MATH_DICT, **context})
        if isinstance(res, float) and res.is_integer(): 
            res = int(res)
        elif isinstance(res, float): 
            res = round(res, 6)
        return res, is_comp, None
    except Exception as e:
        return None, False, str(e)

class NodePropertiesDialog(tk.Toplevel):
    """Окно кастомизации визуальных свойств узла (размеры, пропорции, прозрачность, цвет)."""
    def __init__(self, parent, node_id, n_data):
        super().__init__(parent)
        self.main_app = parent
        self.node_id = node_id
        self.n = n_data
        
        self.title("Свойства оформления узла")
        self.geometry("640x540")
        self.configure(bg="#F3F3F3")
        self.resizable(False, False)
        self.transient(parent)
        self.grab_set()
        
        def_colors = self.main_app.colors.get(self.n["type"], self.main_app.colors["Текст"])
        
        # Подготовка переменных состояния
        self.hide_border = tk.BooleanVar(value=self.n.get("hide_border", False))
        self.hide_content = tk.BooleanVar(value=self.n.get("hide_content", False))
        
        self.border_opacity = tk.DoubleVar(value=self.n.get("border_opacity", 1.0) * 100)
        self.bg_opacity = tk.DoubleVar(value=self.n.get("bg_opacity", 1.0) * 100)
        self.content_opacity = tk.DoubleVar(value=self.n.get("content_opacity", 1.0) * 100)
        
        self.border_color = self.n.get("border_color", def_colors["border"])
        self.bg_color = self.n.get("bg_color", def_colors["bg"])
        
        # Переменные пропорций и геометрии
        self.node_w = tk.IntVar(value=int(self.n.get("w", 200)))
        self.node_h = tk.IntVar(value=int(self.n.get("h", 150)))
        self.lock_aspect = tk.BooleanVar(value=self.n.get("lock_aspect_ratio", False))
        
        current_ratio = self.node_w.get() / self.node_h.get() if self.node_h.get() > 0 else 1.33
        self.aspect_ratio_val = tk.DoubleVar(value=self.n.get("aspect_ratio", current_ratio))
        
        self.result = False
        self.create_ui()
        self.wait_window()

    def create_ui(self):
        main_frame = tk.Frame(self, bg="#F3F3F3")
        main_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=20)
        
        lbl_title = tk.Label(main_frame, text=f"Параметры: {self.n['type']}", font=("Segoe UI", 12, "bold"), bg="#F3F3F3", fg="#1C1C1C")
        lbl_title.pack(anchor=tk.W, pady=(0, 15))
        
        # Двухколоночный макет для опций
        cols_frame = tk.Frame(main_frame, bg="#F3F3F3")
        cols_frame.pack(fill=tk.BOTH, expand=True)
        
        # Левая колонка - Геометрия и пропорции
        left_col = tk.Frame(cols_frame, bg="#F3F3F3")
        left_col.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 10))
        
        lbl_geom = tk.Label(left_col, text="Геометрия и пропорции", font=("Segoe UI", 9, "bold"), bg="#F3F3F3", fg="#5F5F5F")
        lbl_geom.pack(anchor=tk.W, pady=(0, 5))
        
        f_geom = tk.Frame(left_col, bg="#FFFFFF", highlightbackground="#E5E5E5", highlightthickness=1)
        f_geom.pack(fill=tk.BOTH, expand=True, ipady=8)
        
        # Ширина и высота
        f_size = tk.Frame(f_geom, bg="#FFFFFF")
        f_size.pack(fill=tk.X, padx=15, pady=8)
        
        tk.Label(f_size, text="Ширина (px):", font=("Segoe UI", 9), bg="#FFFFFF", fg="#1C1C1C").grid(row=0, column=0, sticky=tk.W, pady=4)
        self.spin_w = tk.Spinbox(f_size, from_=50, to=1200, width=8, textvariable=self.node_w, command=self.on_size_spin, wrap=False)
        self.spin_w.grid(row=0, column=1, sticky=tk.E, padx=(10, 0), pady=4)
        self.spin_w.bind("<KeyRelease>", lambda e: self.on_size_spin())
        
        tk.Label(f_size, text="Высота (px):", font=("Segoe UI", 9), bg="#FFFFFF", fg="#1C1C1C").grid(row=1, column=0, sticky=tk.W, pady=4)
        self.spin_h = tk.Spinbox(f_size, from_=40, to=1000, width=8, textvariable=self.node_h, command=self.on_size_spin, wrap=False)
        self.spin_h.grid(row=1, column=1, sticky=tk.E, padx=(10, 0), pady=4)
        self.spin_h.bind("<KeyRelease>", lambda e: self.on_size_spin())
        
        chk_lock = ttk.Checkbutton(f_geom, text="Сохранять пропорции", variable=self.lock_aspect, command=self.toggle_aspect_lock)
        chk_lock.pack(anchor=tk.W, padx=15, pady=8)
        
        # Выбор пресета пропорций
        lbl_preset = tk.Label(f_geom, text="Соотношение сторон:", font=("Segoe UI", 9), bg="#FFFFFF", fg="#5F5F5F")
        lbl_preset.pack(anchor=tk.W, padx=15, pady=(5, 2))
        
        self.preset_combo = ttk.Combobox(f_geom, values=["Свободно", "1:1 Квадрат", "4:3 Классический", "16:9 Широкий", "2:1 Растянутый"], state="readonly")
        self.preset_combo.pack(fill=tk.X, padx=15, pady=(0, 10))
        self.preset_combo.set("Свободно")
        self.preset_combo.bind("<<ComboboxSelected>>", self.on_preset_selected)
        
        # Базовая видимость
        lbl_vis_title = tk.Label(f_geom, text="Видимость элементов:", font=("Segoe UI", 9), bg="#FFFFFF", fg="#5F5F5F")
        lbl_vis_title.pack(anchor=tk.W, padx=15, pady=(10, 2))
        
        chk_border = ttk.Checkbutton(f_geom, text="Скрыть внешнюю рамку", variable=self.hide_border)
        chk_border.pack(anchor=tk.W, padx=15, pady=4)
        
        chk_content = ttk.Checkbutton(f_geom, text="Скрыть содержимое", variable=self.hide_content)
        chk_content.pack(anchor=tk.W, padx=15, pady=4)

        # Правая колонка - Цвета и прозрачность
        right_col = tk.Frame(cols_frame, bg="#F3F3F3")
        right_col.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(10, 0))
        
        lbl_style = tk.Label(right_col, text="Цветовое оформление", font=("Segoe UI", 9, "bold"), bg="#F3F3F3", fg="#5F5F5F")
        lbl_style.pack(anchor=tk.W, pady=(0, 5))
        
        f_style = tk.Frame(right_col, bg="#FFFFFF", highlightbackground="#E5E5E5", highlightthickness=1)
        f_style.pack(fill=tk.BOTH, expand=True, ipady=8)
        
        # Кнопки выбора цвета
        f_colors = tk.Frame(f_style, bg="#FFFFFF")
        f_colors.pack(fill=tk.X, padx=15, pady=8)
        
        tk.Label(f_colors, text="Цвет контура:", font=("Segoe UI", 9), bg="#FFFFFF", fg="#1C1C1C").pack(side=tk.LEFT, pady=4)
        self.btn_b_color = tk.Button(f_colors, width=5, bg=self.border_color, relief=tk.SOLID, bd=1, command=self.choose_border_color)
        self.btn_b_color.pack(side=tk.RIGHT, pady=4)
        
        f_colors_bg = tk.Frame(f_style, bg="#FFFFFF")
        f_colors_bg.pack(fill=tk.X, padx=15, pady=8)
        
        tk.Label(f_colors_bg, text="Цвет фона:", font=("Segoe UI", 9), bg="#FFFFFF", fg="#1C1C1C").pack(side=tk.LEFT, pady=4)
        self.btn_bg_color = tk.Button(f_colors_bg, width=5, bg=self.bg_color, relief=tk.SOLID, bd=1, command=self.choose_bg_color)
        self.btn_bg_color.pack(side=tk.RIGHT, pady=4)
        
        # Слайдеры прозрачности
        self.create_opacity_slider(f_style, "Прозрачность рамки:", self.border_opacity)
        self.create_opacity_slider(f_style, "Прозрачность фона:", self.bg_opacity)
        self.create_opacity_slider(f_style, "Прозрачность текста:", self.content_opacity)
        
        # Кнопки подтверждения
        f_buttons = tk.Frame(main_frame, bg="#F3F3F3")
        f_buttons.pack(fill=tk.X, pady=(15, 0))
        
        btn_save = ttk.Button(f_buttons, text="Применить", command=self.on_save)
        btn_save.pack(side=tk.RIGHT, padx=(6, 0))
        btn_cancel = ttk.Button(f_buttons, text="Отмена", command=self.destroy)
        btn_cancel.pack(side=tk.RIGHT)

    def create_opacity_slider(self, parent, text, variable):
        frame = tk.Frame(parent, bg="#FFFFFF")
        frame.pack(fill=tk.X, padx=15, pady=6)
        tk.Label(frame, text=text, font=("Segoe UI", 9), bg="#FFFFFF", fg="#1C1C1C", anchor=tk.W).pack(anchor=tk.W)
        
        slider_frame = tk.Frame(frame, bg="#FFFFFF")
        slider_frame.pack(fill=tk.X, pady=2)
        
        slider = ttk.Scale(slider_frame, from_=0, to=100, orient=tk.HORIZONTAL, variable=variable)
        slider.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 10))
        
        lbl_val = tk.Label(slider_frame, text=f"{int(variable.get())}%", font=("Segoe UI", 9, "bold"), bg="#FFFFFF", fg="#0078D4", width=5)
        lbl_val.pack(side=tk.RIGHT)
        
        slider.bind("<Motion>", lambda e: lbl_val.config(text=f"{int(variable.get())}%"))
        slider.bind("<ButtonRelease-1>", lambda e: lbl_val.config(text=f"{int(variable.get())}%"))

    def on_size_spin(self):
        try:
            w = self.node_w.get()
            if self.lock_aspect.get():
                ratio = self.aspect_ratio_val.get()
                if ratio > 0:
                    h = int(w / ratio)
                    self.node_h.set(h)
        except Exception:
            pass

    def toggle_aspect_lock(self):
        if self.lock_aspect.get():
            w = self.node_w.get()
            h = self.node_h.get()
            if h > 0:
                self.aspect_ratio_val.set(w / h)
                self.preset_combo.set("Custom")
        else:
            self.preset_combo.set("Свободно")

    def on_preset_selected(self, event):
        val = self.preset_combo.get()
        if val == "Свободно":
            self.lock_aspect.set(False)
        else:
            self.lock_aspect.set(True)
            if val == "1:1 Квадрат":
                self.aspect_ratio_val.set(1.0)
            elif val == "4:3 Классический":
                self.aspect_ratio_val.set(4.333 / 3.25)
            elif val == "16:9 Широкий":
                self.aspect_ratio_val.set(16.0 / 9.0)
            elif val == "2:1 Растянутый":
                self.aspect_ratio_val.set(2.0)
            self.on_size_spin()

    def choose_border_color(self):
        color = colorchooser.askcolor(initialcolor=self.border_color, title="Выберите цвет рамки")
        if color[1]:
            self.border_color = color[1]
            self.btn_b_color.config(bg=self.border_color)
            
    def choose_bg_color(self):
        color = colorchooser.askcolor(initialcolor=self.bg_color, title="Выберите цвет фона")
        if color[1]:
            self.bg_color = color[1]
            self.btn_bg_color.config(bg=self.bg_color)

    def on_save(self):
        self.n["hide_border"] = self.hide_border.get()
        self.n["hide_content"] = self.hide_content.get()
        self.n["border_color"] = self.border_color
        self.n["bg_color"] = self.bg_color
        self.n["border_opacity"] = self.border_opacity.get() / 100.0
        self.n["bg_opacity"] = self.bg_opacity.get() / 100.0
        self.n["content_opacity"] = self.content_opacity.get() / 100.0
        
        self.n["w"] = self.node_w.get()
        self.n["h"] = self.node_h.get()
        self.n["lock_aspect_ratio"] = self.lock_aspect.get()
        self.n["aspect_ratio"] = self.aspect_ratio_val.get()
        
        self.result = True
        self.destroy()

class NodeEditorDialog(tk.Toplevel):
    """Редактор текстового содержимого узлов с навигатором переменных."""
    def __init__(self, parent, node_type, initial_content="", subtype=""):
        super().__init__(parent)
        self.main_app = parent
        self.title(f"Редактор: {node_type}")
        self.geometry("820x580")
        self.configure(bg="#F3F3F3")
        self.transient(parent)
        self.grab_set()
        
        self.result = None
        self.node_type = node_type
        self.vars_dict = self.main_app.get_current_vars() if hasattr(self.main_app, 'get_current_vars') else {}
        
        self.create_ui(initial_content)
        self.wait_window()

    def create_ui(self, initial_content):
        main_frame = tk.Frame(self, bg="#F3F3F3")
        main_frame.pack(fill=tk.BOTH, expand=True, padx=16, pady=16)

        self.pane = ttk.PanedWindow(main_frame, orient=tk.HORIZONTAL)
        self.pane.pack(fill=tk.BOTH, expand=True)
        
        self.editor_frame = tk.Frame(self.pane, bg="#F3F3F3")
        self.pane.add(self.editor_frame, weight=3)
        
        instructions = {
            "Код": "Первая строка - язык (например, python).\nДалее код. (Ctrl+Enter для сохранения)",
            "Переменная": "Опишите переменные (каждая с новой строки).\nФормат: Имя = Значение (Например: Speed = 50)\nВычисляемые: Y = {X} + 10",
            "Сводка": "Таблица данных. 1-я строка - Имя, 2-я - Заголовки, далее - данные.\nПример: \nCars\nModel, Price\nBMW, 5000",
            "Страница": "Введите HTML5 и CSS (внутри <style>).\nИспользуйте {переменные} для вывода данных.",
            "Функция": "Введите функцию или выражение:\nПоддерживается вызов {Таблица}.строка.значение\nИли {Список}[0].значение",
            "Ссылка": "Введите URL или путь к файлу.\nНажмите кнопку перехода на узле для открытия.",
        }.get(self.node_type, "Введите содержимое узла.\nИспользуйте фигурные скобки {Переменные} для подстановки.")
        
        lbl_info = tk.Label(self.editor_frame, text=instructions, font=("Segoe UI", 9), fg="#5F5F5F", bg="#F3F3F3", justify=tk.LEFT, anchor=tk.W)
        lbl_info.pack(fill=tk.X, pady=(0, 8))
        
        self.font_family = "Consolas" if self.node_type in ["Код", "Сводка"] else "Segoe UI"
        
        self.text_area_frame = tk.Frame(self.editor_frame, bg="#FFFFFF", highlightbackground="#E5E5E5", highlightthickness=1)
        self.text_area_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 10))
        
        text_scroll = ttk.Scrollbar(self.text_area_frame)
        text_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.text_area = tk.Text(
            self.text_area_frame, font=(self.font_family, 11), 
            relief=tk.FLAT, bd=0, bg="#FFFFFF", fg="#1C1C1C",
            insertbackground="#0078D4", insertwidth=2, padx=12, pady=12,
            yscrollcommand=text_scroll.set
        )
        self.text_area.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        text_scroll.config(command=self.text_area.yview)
        
        self.text_area.insert(tk.END, initial_content)
        self.text_area.bind("<Control-Return>", self.on_ctrl_enter)
        self.text_area.bind("<KeyRelease>", self.on_key_release)
        
        if self.node_type == "Функция":
            self.eval_frame = tk.Frame(self.editor_frame, bg="#FFFFFF", highlightbackground="#E5E5E5", highlightthickness=1)
            self.eval_frame.pack(fill=tk.X, pady=(0, 10))
            self.eval_lbl = tk.Label(self.eval_frame, text="Результат вычисления: ...", font=("Segoe UI", 10, "bold"), bg="#FFFFFF", fg="#0078D4", anchor=tk.W)
            self.eval_lbl.pack(fill=tk.X, padx=12, pady=10)
            self.after(50, self.on_text_change)
            
        # --- ПРАВАЯ ПАНЕЛЬ (Навигатор) ---
        self.tools_frame = tk.Frame(self.pane, bg="#F3F3F3")
        self.pane.add(self.tools_frame, weight=1)
        
        self.notebook = ttk.Notebook(self.tools_frame)
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=(10, 0))
        
        self.tab_vars = tk.Frame(self.notebook, bg="#FFFFFF")
        self.notebook.add(self.tab_vars, text="Данные")
        
        tree_scroll = ttk.Scrollbar(self.tab_vars)
        tree_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.tree_vars = ttk.Treeview(self.tab_vars, columns=("Type", "Name"), show="headings", yscrollcommand=tree_scroll.set)
        self.tree_vars.heading("Type", text="Тип")
        self.tree_vars.heading("Name", text="Имя")
        self.tree_vars.column("Type", width=70, anchor=tk.CENTER)
        self.tree_vars.column("Name", width=120, anchor=tk.W)
        self.tree_vars.pack(fill=tk.BOTH, expand=True, pady=5, padx=5)
        tree_scroll.config(command=self.tree_vars.yview)
        
        self.populate_vars_tree()
        self.tree_vars.bind("<Double-1>", self.on_tree_double_click)
        
        lbl_hint = tk.Label(self.tab_vars, text="Двойной клик для вставки", font=("Segoe UI", 8), fg="#7A7A7A", bg="#FFFFFF")
        lbl_hint.pack(pady=4)

        self.tab_ops = tk.Frame(self.notebook, bg="#FFFFFF")
        self.notebook.add(self.tab_ops, text="Вставка")
        self.create_operators_tab()
        
        btn_frame = tk.Frame(main_frame, bg="#F3F3F3")
        btn_frame.pack(fill=tk.X, pady=(6, 0))
        
        save_btn = ttk.Button(btn_frame, text="Сохранить (Ctrl+Enter)", command=self.on_ok)
        save_btn.pack(side=tk.RIGHT, padx=(6, 0))
        cancel_btn = ttk.Button(btn_frame, text="Отмена", command=self.destroy)
        cancel_btn.pack(side=tk.RIGHT)
        
        self.after(50, self.highlight_syntax)
        self.text_area.focus_set()

    def populate_vars_tree(self):
        for item in self.tree_vars.get_children():
            self.tree_vars.delete(item)
            
        for k, v in self.vars_dict.items():
            if isinstance(v, DataTable):
                node = self.tree_vars.insert("", tk.END, values=("Таблица", k), tags=("table",))
                for header in v.headers:
                    self.tree_vars.insert(node, tk.END, values=("Колонка", f".{header}"), tags=("subitem",))
            elif isinstance(v, (int, float)):
                self.tree_vars.insert("", tk.END, values=("Число", k), tags=("var",))
            else:
                self.tree_vars.insert("", tk.END, values=("Строка", k), tags=("var",))
                
        self.tree_vars.tag_configure("table", foreground="#B45309", font=("Segoe UI", 9, "bold"))
        self.tree_vars.tag_configure("var", foreground="#0078D4", font=("Segoe UI", 9, "bold"))
        self.tree_vars.tag_configure("subitem", foreground="#5F5F5F")

    def on_tree_double_click(self, event):
        item_id = self.tree_vars.focus()
        if not item_id: 
            return
        
        values = self.tree_vars.item(item_id, "values")
        if not values: 
            return
        
        val_type, val_name = values
        
        if val_type == "Колонка":
            parent_id = self.tree_vars.parent(item_id)
            parent_values = self.tree_vars.item(parent_id, "values")
            table_name = parent_values[1]
            insert_text = f"{{{table_name}}}[0]{val_name}"
        else:
            insert_text = f"{{{val_name}}}"
            
        self.text_area.insert(tk.INSERT, insert_text)
        self.highlight_syntax()
        if self.node_type == "Функция":
            self.on_text_change()
        self.text_area.focus_set()

    def create_operators_tab(self):
        container = tk.Frame(self.tab_ops, bg="#FFFFFF")
        container.pack(fill=tk.BOTH, expand=True, padx=8, pady=8)
        
        symbols = [
            ("Корень", "√("), ("Квадрат", "²"), ("Куб", "³"),
            ("Пи", "π"), ("Беск", "∞"),
            ("sin()", "sin("), ("cos()", "cos("), ("tan()", "tan("),
            ("sum()", "sum("), ("len()", "len("),
            ("≠", " ≠ "), ("≤", " ≤ "), ("≥", " ≥ ")
        ]
        
        row, col = 0, 0
        container.grid_columnconfigure(0, weight=1)
        container.grid_columnconfigure(1, weight=1)
        
        for label, symbol in symbols:
            btn = ttk.Button(container, text=label, command=lambda s=symbol: self.insert_symbol(s))
            btn.grid(row=row, column=col, padx=3, pady=3, sticky=tk.EW)
            col += 1
            if col > 1:
                col = 0
                row += 1
                
        if self.node_type == "Функция":
            lbl_tit = tk.Label(container, text="Примеры выражений:", font=("Segoe UI", 9, "bold"), bg="#FFFFFF", fg="#1C1C1C")
            lbl_tit.grid(row=row+1, column=0, columnspan=2, pady=(12, 4), sticky=tk.W)
            templates = [
                "{Таблица}[0].Колонка + 10",
                "sum({Таблица}.Колонка)",
                "100 >= 50",
                "sqrt({X}*2 + {Y}*2)"
            ]
            for i, t in enumerate(templates):
                btn = ttk.Button(container, text=t, command=lambda text=t: self.replace_text(text))
                btn.grid(row=row+2+i, column=0, columnspan=2, padx=3, pady=3, sticky=tk.EW)

    def insert_symbol(self, symbol):
        self.text_area.insert(tk.INSERT, symbol)
        self.text_area.focus_set()
        self.highlight_syntax()
        if self.node_type == "Функция":
            self.on_text_change()
            
    def replace_text(self, text):
        self.text_area.delete("1.0", tk.END)
        self.text_area.insert(tk.END, text)
        self.highlight_syntax()
        if self.node_type == "Функция":
            self.on_text_change()

    def highlight_syntax(self):
        for tag in ["variable", "bracket", "keyword", "number"]:
            self.text_area.tag_remove(tag, "1.0", tk.END)
            
        self.text_area.tag_config("variable", background="#E1F0FE", foreground="#0078D4", font=(self.font_family, 11, "bold"))
        self.text_area.tag_config("bracket", foreground="#0F766E", font=(self.font_family, 11, "bold"))
        self.text_area.tag_config("keyword", foreground="#0078D4", font=(self.font_family, 11, "bold"))
        self.text_area.tag_config("number", foreground="#0F766E")
        
        text_content = self.text_area.get("1.0", tk.END)
        
        countVar = tk.StringVar()
        pos = "1.0"
        while True:
            pos = self.text_area.search(r"\{[^}]*\}", pos, stopindex=tk.END, regexp=True, count=countVar)
            if not pos: 
                break
            end_pos = f"{pos}+{countVar.get()}c"
            self.text_area.tag_add("variable", pos, end_pos)
            pos = end_pos
            
        pos = "1.0"
        while True:
            pos = self.text_area.search(r"\}(?:\[[^\]]+\]|\.[a-zA-Z0-9_]+)+", pos, stopindex=tk.END, regexp=True, count=countVar)
            if not pos: 
                break
            start_mod = f"{pos}+1c"
            end_pos = f"{pos}+{countVar.get()}c"
            self.text_area.tag_add("variable", start_mod, end_pos)
            pos = end_pos

    def on_key_release(self, event):
        self.highlight_syntax()
        if self.node_type == "Функция":
            self.on_text_change()

    def on_ctrl_enter(self, event):
        self.on_ok()
        return "break"

    def on_text_change(self, event=None):
        if self.node_type != "Функция": 
            return
        expr = self.text_area.get(1.0, tk.END).strip()
        
        if not expr:
            self.eval_lbl.config(text="Результат вычисления: ...", fg="#7A7A7A")
            self.eval_frame.config(bg="#FFFFFF")
            return

        result, is_comp, err_msg = evaluate_math_expression(expr, self.vars_dict)

        if err_msg and "name" in err_msg and "is not defined" in err_msg:
            err_msg = "Ожидание ввода данных..."

        if err_msg:
            self.eval_lbl.config(text=f"Статус: {err_msg}", fg="#B45309")
            self.eval_frame.config(bg="#FFFBEB")
        else:
            if isinstance(result, bool):
                if result:
                    self.eval_lbl.config(text="Логика: ИСТИНА", fg="#0F766E")
                    self.eval_frame.config(bg="#F0FDF4")
                else:
                    self.eval_lbl.config(text="Логика: ЛОЖЬ", fg="#E11D48")
                    self.eval_frame.config(bg="#FFF1F2")
            else:
                self.eval_lbl.config(text=f"Результат: {result}", fg="#0078D4")
                self.eval_frame.config(bg="#F0F9FF")

    def on_ok(self):
        self.result = self.text_area.get(1.0, tk.END).strip()
        self.destroy()

class DiagramPlanner(tk.Tk):
    def __init__(self):
        super().__init__()
        
        # Настройка единого плоского стиля интерфейса
        style = ttk.Style()
        style.theme_use('clam')
        
        style.configure(".", background="#F3F3F3", foreground="#1C1C1C", font=("Segoe UI", 10))
        
        style.configure("TButton", 
                        background="#FFFFFF", 
                        foreground="#1C1C1C", 
                        bordercolor="#E5E5E5", 
                        lightcolor="#E5E5E5", 
                        darkcolor="#E5E5E5", 
                        relief="flat", 
                        padding=(10, 5), 
                        font=("Segoe UI", 9))
        style.map("TButton", 
                  background=[("active", "#EAEAEA"), ("pressed", "#DFDFDF")],
                  bordercolor=[("active", "#CCCCCC")])

        style.configure("TNotebook", background="#F3F3F3", bordercolor="#E5E5E5", padding=2)
        style.configure("TNotebook.Tab", background="#F3F3F3", foreground="#5F5F5F", bordercolor="#E5E5E5", padding=(12, 4))
        style.map("TNotebook.Tab", background=[("selected", "#FFFFFF")], foreground=[("selected", "#0078D4")])
        
        style.configure("Vertical.TScrollbar", gripcount=0, background="#FFFFFF", troughcolor="#F3F3F3", bordercolor="#E5E5E5", arrowcolor="#5F5F5F")
        style.configure("Toolbutton", background="#F3F3F3", relief="flat", bordercolor="#F3F3F3", padding=5)
        style.map("Toolbutton", background=[("active", "#EAEAEA"), ("selected", "#FFFFFF")])

        self.current_filename = None
        self.is_modified = False
        
        self.geometry("1400x850")
        self.update_window_title()
        self.protocol("WM_DELETE_WINDOW", self.on_closing)

        self.nodes = {}
        self.edges = []
        self.node_counter = 0
        self.internal_clipboard = None
        
        self.image_cache = {} 
        self.source_image_cache = {} 
        self.animated_items = {} 
        self.anim_ticks = {} 
        self._render_timer = None 
        self._cached_vars = {}
        
        self.colors = {
            "Текст": {"bg": "#FFFFFF", "border": "#0078D4", "header": "#F0F9FF"},
            "Функция": {"bg": "#FFFFFF", "border": "#8B5CF6", "header": "#F5F3FF"},
            "Переменная": {"bg": "#FFFFFF", "border": "#EF4444", "header": "#FEF2F2"},
            "Регулятор": {"bg": "#FFFFFF", "border": "#06B6D4", "header": "#ECFEFF"},
            "Код": {"bg": "#202020", "border": "#2D2D2D", "header": "#2D2D2D"},
            "Таблица": {"bg": "#FFFFFF", "border": "#10B981", "header": "#ECFDF5"},
            "Список": {"bg": "#FFFFFF", "border": "#F59E0B", "header": "#FFFBEB"},
            "Прогресс бар": {"bg": "#FFFFFF", "border": "#EC4899", "header": "#FDF2F8"},
            "Страница": {"bg": "#FFFFFF", "border": "#6B7280", "header": "#F9FAFB"},
            "Изображение": {"bg": "#FFFFFF", "border": "#9CA3AF", "header": "#F9FAFB"},
            "Диаграмма": {"bg": "#FFFFFF", "border": "#6366F1", "header": "#EEF2FF"},
            "Секторная диаграмма": {"bg": "#FFFFFF", "border": "#8B5CF6", "header": "#F5F3FF"},
            "Переключатель": {"bg": "#FFFFFF", "border": "#14B8A6", "header": "#F0FDFA"},
            "Ссылка": {"bg": "#FFFFFF", "border": "#0078D4", "header": "#F0F9FF"},
            "Часы": {"bg": "#1C1C1C", "border": "#EF4444", "header": "#2D2D2D"},
            "Сводка": {"bg": "#FFFFFF", "border": "#F59E0B", "header": "#FFFBEB"},
            "Магнитола": {"bg": "#1C1C1C", "border": "#0EA5E9", "header": "#111827"},
            "Контроллер": {"bg": "#FFFFFF", "border": "#7C3AED", "header": "#F5F3FF"}
        }

        self.themes = {
            "Aero (Белый)": {"app_bg": "#F3F3F3", "toolbar_bg": "#FFFFFF", "accent": "#0078D4", "canvas_bg": "#FFFFFF"},
            "Windows 7 Aero (Синий)": {"app_bg": "#DDEBF7", "toolbar_bg": "#EAF3FB", "accent": "#3D7FCB", "canvas_bg": "#F5F9FD"},
            "Windows XP (Синий)": {"app_bg": "#ECE9D8", "toolbar_bg": "#D6E4F7", "accent": "#0A4FA3", "canvas_bg": "#FFFFFF"}
        }
        self.current_theme = "Aero (Белый)"

        self.snap_to_grid = tk.BooleanVar(value=True)
        self.view_mode = tk.BooleanVar(value=False) 
        self.grid_size = 20

        self.offset_x, self.offset_y = 0, 0
        self.zoom_level = 1.0  
        self.pan_start_x, self.pan_start_y = 0, 0
        self.space_pressed = False
        self.mouse_pos = (0, 0)

        self.history = []
        self.history_index = -1
        self.selected_node = None
        self.selected_edge = None
        self.connecting_from = None
        self.drag_data = {"x": 0, "y": 0}
        self.panning = False
        self.resizing_node = None 
        self.active_slider = None 

        self.show_sidebar = tk.BooleanVar(value=True)

        self.init_ui()
        self.save_state(initial=True)
        self.update_animations()
        self.update_status("Готово. Нажмите F1 для справки.")

    def update_window_title(self):
        display_name = os.path.basename(self.current_filename) if self.current_filename else "Безымянный"
        dirty_star = "*" if self.is_modified else ""
        self.title(f"{display_name}{dirty_star} — MindsMap")

    def _stop_all_playback(self):
        for n in self.nodes.values():
            if n.get("type") == "Магнитола" and n.get("is_playing"):
                n["is_playing"] = False
                n["play_started_at"] = None
        self._magnitola_stop_playback()

    def on_closing(self):
        self._stop_all_playback()
        if self.is_modified:
            result = messagebox.askyesnocancel(
                "Сохранить изменения?", 
                "Схема была изменена.\nСохранить перед выходом?",
                icon='warning'
            )
            if result is True:
                if self.save_file(): 
                    self.destroy()
            elif result is False:
                self.destroy()
        else:
            self.destroy()

    def init_ui(self):
        menubar = tk.Menu(self, bg="#F3F3F3", fg="#1C1C1C", relief="flat")
        
        file_menu = tk.Menu(menubar, tearoff=0, bg="#FFFFFF", activebackground="#EAEAEA")
        file_menu.add_command(label="Создать новый", command=self.new_file, accelerator="Ctrl+N")
        file_menu.add_command(label="Открыть...", command=self.load_file, accelerator="Ctrl+O")
        file_menu.add_command(label="Сохранить...", command=self.save_file, accelerator="Ctrl+S")
        file_menu.add_separator()
        file_menu.add_command(label="Экспорт в PNG", command=self.export_to_image, accelerator="Ctrl+E")
        file_menu.add_separator()
        file_menu.add_command(label="Выход", command=self.on_closing, accelerator="Alt+F4")
        menubar.add_cascade(label="Файл", menu=file_menu)

        edit_menu = tk.Menu(menubar, tearoff=0, bg="#FFFFFF", activebackground="#EAEAEA")
        edit_menu.add_command(label="Отменить", command=self.undo, accelerator="Ctrl+Z")
        edit_menu.add_command(label="Повторить", command=self.redo, accelerator="Ctrl+Y")
        edit_menu.add_separator()
        edit_menu.add_command(label="Копировать узел", command=self.on_copy, accelerator="Ctrl+C")
        edit_menu.add_command(label="Вырезать узел", command=self.on_cut, accelerator="Ctrl+X")
        edit_menu.add_command(label="Вставить", command=self.on_paste, accelerator="Ctrl+V")
        edit_menu.add_separator()
        edit_menu.add_command(label="Дублировать", command=self.duplicate_node, accelerator="Ctrl+D")
        edit_menu.add_command(label="Удалить выбранное", command=self.delete_node, accelerator="Delete")
        edit_menu.add_separator()
        edit_menu.add_checkbutton(label="Режим просмотра", variable=self.view_mode, command=self.toggle_view_mode, accelerator="F3")
        edit_menu.add_command(label="Выровнять все по сетке", command=self.align_all_to_grid)
        edit_menu.add_checkbutton(label="Привязка к сетке", variable=self.snap_to_grid)
        edit_menu.add_separator()
        edit_menu.add_command(label="Очистить холст", command=self.clear_canvas)
        menubar.add_cascade(label="Правка", menu=edit_menu)
        
        view_menu = tk.Menu(menubar, tearoff=0, bg="#FFFFFF", activebackground="#EAEAEA")
        view_menu.add_command(label="Приблизить", command=lambda: self.do_zoom(1.1), accelerator="Ctrl++")
        view_menu.add_command(label="Отдалить", command=lambda: self.do_zoom(0.9), accelerator="Ctrl+-")
        view_menu.add_command(label="Сбросить масштаб 100%", command=self.reset_zoom, accelerator="Ctrl+0")
        view_menu.add_separator()
        view_menu.add_command(label="Показать/скрыть навигатор", command=self.toggle_sidebar)
        menubar.add_cascade(label="Вид", menu=view_menu)

        pref_menu = tk.Menu(menubar, tearoff=0, bg="#FFFFFF", activebackground="#EAEAEA")
        self.theme_var = tk.StringVar(value=self.current_theme)
        theme_menu = tk.Menu(pref_menu, tearoff=0, bg="#FFFFFF", activebackground="#EAEAEA")
        for theme_name in self.themes:
            theme_menu.add_radiobutton(label=theme_name, variable=self.theme_var, value=theme_name, command=lambda t=theme_name: self.apply_theme(t))
        pref_menu.add_cascade(label="Цветовая тема", menu=theme_menu)
        pref_menu.add_checkbutton(label="Привязка к сетке", variable=self.snap_to_grid)
        pref_menu.add_command(label="Размер сетки...", command=self.change_grid_size)
        menubar.add_cascade(label="Преференс", menu=pref_menu)

        help_menu = tk.Menu(menubar, tearoff=0, bg="#FFFFFF", activebackground="#EAEAEA")
        help_menu.add_command(label="Горячие клавиши", command=self.show_help, accelerator="F1")
        help_menu.add_separator()
        help_menu.add_command(label="О программе", command=self.show_about)
        menubar.add_cascade(label="Справка", menu=help_menu)

        self.config(menu=menubar)

        self.main_pane = ttk.PanedWindow(self, orient=tk.HORIZONTAL)
        self.main_pane.pack(fill=tk.BOTH, expand=True)

        self.sidebar_frame = tk.Frame(self.main_pane, bg="#F3F3F3", width=250)
        self.main_pane.add(self.sidebar_frame, weight=1)
        
        f_search = tk.Frame(self.sidebar_frame, bg="#F3F3F3")
        f_search.pack(fill=tk.X, padx=12, pady=(15, 8))
        
        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", lambda *args: self.filter_navigator_nodes())
        
        self.ent_search = tk.Entry(
            f_search, textvariable=self.search_var, font=("Segoe UI", 10),
            bg="#FFFFFF", fg="#1C1C1C", insertbackground="#0078D4",
            relief=tk.FLAT, bd=0, highlightthickness=1, highlightbackground="#E5E5E5", highlightcolor="#0078D4"
        )
        self.ent_search.pack(fill=tk.X, ipady=6, padx=2)
        self.ent_search.insert(0, "Поиск узлов...")
        self.ent_search.bind("<FocusIn>", lambda e: self.ent_search.delete(0, tk.END) if self.ent_search.get() == "Поиск узлов..." else None)
        self.ent_search.bind("<FocusOut>", lambda e: self.ent_search.insert(0, "Поиск узлов...") if not self.ent_search.get() else None)

        f_nav_tree = tk.Frame(self.sidebar_frame, bg="#FFFFFF", highlightbackground="#E5E5E5", highlightthickness=1)
        f_nav_tree.pack(fill=tk.BOTH, expand=True, padx=12, pady=(0, 15))
        
        scroll_nav = ttk.Scrollbar(f_nav_tree)
        scroll_nav.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.nav_tree = ttk.Treeview(f_nav_tree, columns=("Type"), show="headings", yscrollcommand=scroll_nav.set)
        self.nav_tree.heading("Type", text="Узлы схемы")
        self.nav_tree.column("Type", anchor=tk.W)
        self.nav_tree.pack(fill=tk.BOTH, expand=True)
        scroll_nav.config(command=self.nav_tree.yview)
        
        self.nav_tree.bind("<Double-1>", self.on_navigator_double_click)

        self.right_container = tk.Frame(self.main_pane, bg="#F3F3F3")
        self.main_pane.add(self.right_container, weight=4)

        self.toolbar = tk.Frame(self.right_container, bg="#FFFFFF", height=45, bd=0, highlightbackground="#E5E5E5", highlightthickness=1)
        self.toolbar.pack(side=tk.TOP, fill=tk.X)
        
        t_pad = {"padx": 3, "pady": 6}
        
        ttk.Button(self.toolbar, text="Новый", command=self.new_file).pack(side=tk.LEFT, **t_pad)
        ttk.Button(self.toolbar, text="Сохранить", command=self.save_file).pack(side=tk.LEFT, **t_pad)
        
        sep1 = tk.Frame(self.toolbar, width=1, bg="#E5E5E5")
        sep1.pack(side=tk.LEFT, fill=tk.Y, padx=8, pady=6)
        
        ttk.Button(self.toolbar, text="Навигатор", command=self.toggle_sidebar).pack(side=tk.LEFT, **t_pad)
        ttk.Checkbutton(self.toolbar, text="Режим просмотра (F3)", variable=self.view_mode, style="Toolbutton", command=self.toggle_view_mode).pack(side=tk.LEFT, **t_pad)
        
        sep2 = tk.Frame(self.toolbar, width=1, bg="#E5E5E5")
        sep2.pack(side=tk.LEFT, fill=tk.Y, padx=8, pady=6)
        
        ttk.Button(self.toolbar, text="Текст", command=lambda: self.create_node("Текст")).pack(side=tk.LEFT, **t_pad)
        ttk.Button(self.toolbar, text="Переменная", command=lambda: self.create_node("Переменная", initial="Index = 0")).pack(side=tk.LEFT, **t_pad)
        ttk.Button(self.toolbar, text="Сводка", command=lambda: self.create_node("Сводка", initial="Таблица1\nName, Value\nItemA, 25\nItemB, 50")).pack(side=tk.LEFT, **t_pad)
        ttk.Button(self.toolbar, text="Функция", command=lambda: self.create_node("Функция", initial="{Таблица1}[Index].Value + 50")).pack(side=tk.LEFT, **t_pad)
        ttk.Button(self.toolbar, text="Магнитола", command=lambda: self.create_node("Магнитола")).pack(side=tk.LEFT, **t_pad)
        ttk.Button(self.toolbar, text="Контроллер", command=lambda: self.create_node("Контроллер")).pack(side=tk.LEFT, **t_pad)
        
        sep3 = tk.Frame(self.toolbar, width=1, bg="#E5E5E5")
        sep3.pack(side=tk.LEFT, fill=tk.Y, padx=8, pady=6)
        
        ttk.Button(self.toolbar, text="Связать", command=self.start_connection_from_selected).pack(side=tk.LEFT, **t_pad)

        self.zoom_label = tk.Label(self.toolbar, text="100%", background="#FFFFFF", font=("Segoe UI", 9, "bold"), fg="#0078D4")
        self.zoom_label.pack(side=tk.RIGHT, padx=16)

        self.canvas = tk.Canvas(self.right_container, bg="#FFFFFF", highlightthickness=0)
        self.canvas.pack(fill=tk.BOTH, expand=True)

        self.status_bar = tk.Label(self.right_container, text="Готово", bg="#F3F3F3", fg="#5F5F5F", anchor=tk.W, padx=12, pady=5, bd=0, font=("Segoe UI", 8))
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)

        self.canvas.bind("<Motion>", self.on_mouse_move)
        self.canvas.bind("<Button-1>", self.on_lmb_down)
        self.canvas.bind("<Double-Button-1>", self.on_double_click)
        self.canvas.bind("<B1-Motion>", self.on_lmb_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_lmb_up)
        self.canvas.bind("<Button-3>", self.on_rmb_down)
        self.canvas.bind("<Button-2>", self.on_pan_start)
        self.canvas.bind("<B2-Motion>", self.on_pan_drag)

        self.bind("<Control-z>", lambda e: self.undo())
        self.bind("<Control-y>", lambda e: self.redo())
        self.bind("<Control-s>", lambda e: self.save_file())
        self.bind("<Control-o>", lambda e: self.load_file())
        self.bind("<Control-n>", lambda e: self.new_file())
        self.bind("<Control-c>", self.on_copy)
        self.bind("<Control-x>", self.on_cut)
        self.bind("<Control-v>", self.on_paste)
        self.bind("<Control-d>", lambda e: self.duplicate_node())
        self.bind("<Control-e>", lambda e: self.export_to_image())
        self.bind("<Delete>", lambda e: self.delete_node())
        self.bind("<Escape>", self.on_escape)
        self.bind("<F1>", lambda e: self.show_help())
        self.bind("<F2>", lambda e: self.edit_node() if self.selected_node else None)
        self.bind("<F3>", lambda e: self.toggle_view_mode(from_key=True))
        
        self.bind("<Control-plus>", lambda e: self.do_zoom(1.1))
        self.bind("<Control-equal>", lambda e: self.do_zoom(1.1))
        self.bind("<Control-minus>", lambda e: self.do_zoom(0.9))
        self.bind("<Control-0>", lambda e: self.reset_zoom())
        
        self.canvas.bind("<Control-MouseWheel>", self.on_mouse_wheel)
        self.canvas.bind("<Control-Button-4>", lambda e: self.do_zoom(1.1, e.x, e.y))
        self.canvas.bind("<Control-Button-5>", lambda e: self.do_zoom(0.9, e.x, e.y))
        
        self.bind("<KeyPress-space>", self.on_space_down)
        self.bind("<KeyRelease-space>", self.on_space_up)
        self.bind("<Up>", lambda e: self.pan_by(0, 30))
        self.bind("<Down>", lambda e: self.pan_by(0, -30))
        self.bind("<Left>", lambda e: self.pan_by(30, 0))
        self.bind("<Right>", lambda e: self.pan_by(-30, 0))

        self.setup_context_menus()

    def color_to_hex(self, color_name):
        """Конвертирует любое название цвета Tkinter в шестнадцатеричную HEX-строку."""
        try:
            rgb = self.winfo_rgb(color_name)
            r, g, b = rgb[0] >> 8, rgb[1] >> 8, rgb[2] >> 8
            return f"#{r:02x}{g:02x}{b:02x}"
        except Exception:
            if str(color_name).startswith("#"):
                return color_name
            return "#FFFFFF"

    def blend_color(self, hex_color, bg_hex="#FFFFFF", alpha=1.0):
        """Смешивает HEX-цвет с фоном холста в зависимости от прозрачности, имитируя альфа-канал."""
        if alpha >= 1.0: 
            return hex_color
        if alpha <= 0.0: 
            return bg_hex
            
        c_hex = self.color_to_hex(hex_color).lstrip('#')
        b_hex = self.color_to_hex(bg_hex).lstrip('#')
        
        try:
            r1, g1, b1 = int(c_hex[0:2], 16), int(c_hex[2:4], 16), int(c_hex[4:6], 16)
            r2, g2, b2 = int(b_hex[0:2], 16), int(b_hex[2:4], 16), int(b_hex[4:6], 16)
            
            r = int(r1 * alpha + r2 * (1.0 - alpha))
            g = int(g1 * alpha + g2 * (1.0 - alpha))
            b = int(b1 * alpha + b2 * (1.0 - alpha))
            
            return f"#{r:02x}{g:02x}{b:02x}"
        except Exception:
            return hex_color

    def get_contrasting_text_color(self, bg_hex, bg_opacity, canvas_bg="#FFFFFF"):
        """Рассчитывает относительную яркость фона для автоматического выбора черного или белого цвета текста."""
        blended = self.blend_color(bg_hex, canvas_bg, bg_opacity)
        hex_val = blended.lstrip('#')
        try:
            r, g, b = int(hex_val[0:2], 16), int(hex_val[2:4], 16), int(hex_val[4:6], 16)
        except Exception:
            return "#1C1C1C"
        # Формула стандарта W3C для оценки относительной яркости
        lum = (0.299 * r + 0.587 * g + 0.114 * b) / 255.0
        return "#1C1C1C" if lum > 0.5 else "#FFFFFF"

    def apply_theme(self, theme_name):
        theme = self.themes.get(theme_name)
        if not theme:
            return
        self.current_theme = theme_name
        self.configure(bg=theme["app_bg"])
        self.sidebar_frame.configure(bg=theme["app_bg"])
        self.toolbar.configure(bg=theme["toolbar_bg"])
        self.right_container.configure(bg=theme["app_bg"])
        self.status_bar.configure(bg=theme["app_bg"])
        self.canvas.configure(bg=theme["canvas_bg"])
        self.zoom_label.configure(background=theme["toolbar_bg"], fg=theme["accent"])
        style = ttk.Style()
        style.configure(".", background=theme["app_bg"])
        style.configure("TButton", background=theme["toolbar_bg"])
        style.map("TButton", background=[("active", theme["app_bg"]), ("pressed", theme["app_bg"])])
        self.render()
        self.update_status(f"Применена тема: {theme_name}")

    def change_grid_size(self):
        val = simpledialog.askinteger("Размер сетки", "Шаг сетки (px):", initialvalue=self.grid_size, minvalue=5, maxvalue=200)
        if val:
            self.grid_size = val
            self.update_status(f"Размер сетки: {val}px")

    def toggle_sidebar(self):
        if self.show_sidebar.get():
            self.main_pane.forget(self.sidebar_frame)
            self.show_sidebar.set(False)
            self.update_status("Навигатор скрыт")
        else:
            self.main_pane.insert(0, self.sidebar_frame, weight=1)
            self.show_sidebar.set(True)
            self.update_status("Навигатор отображен")
            self.update_navigator_list()

    def update_navigator_list(self):
        for item in self.nav_tree.get_children():
            self.nav_tree.delete(item)
            
        query = self.search_var.get().strip().lower()
        if query == "поиск узлов...":
            query = ""
            
        for node_id, n in self.nodes.items():
            content_preview = n["content"].split("\n")[0][:25]
            display_text = f"[{n['type']}] {content_preview}"
            
            if query and query not in display_text.lower():
                continue
                
            self.nav_tree.insert("", tk.END, iid=node_id, values=(display_text,))

    def filter_navigator_nodes(self):
        self.update_navigator_list()

    def on_navigator_double_click(self, event):
        node_id = self.nav_tree.focus()
        if not node_id or node_id not in self.nodes:
            return
            
        n = self.nodes[node_id]
        cw = self.canvas.winfo_width()
        ch = self.canvas.winfo_height()
        if cw <= 1: 
            cw = self.winfo_width()
        if ch <= 1: 
            ch = self.winfo_height()
            
        s = n.get("scale", 1.0)
        n_cx = n["x"] + (n["w"] * s) / 2
        n_cy = n["y"] + (n["h"] * s) / 2
        
        self.zoom_level = 1.0
        self.offset_x = (cw / 2) - n_cx
        self.offset_y = (ch / 2) - n_cy
        
        self.zoom_label.config(text="100%")
        
        if self.selected_node:
            self.set_node_selected(self.selected_node, False)
        self.selected_node = node_id
        self.selected_edge = None
        self.set_node_selected(node_id, True)
        
        self.render()
        self.update_status(f"Фокус на узле: {n['type']} (X: {int(n['x'])}, Y: {int(n['y'])})")

    def show_about(self):
        about_text = (
            "MindsMap — Professional Diagram Modeler\n\n"
            "Версия: 2.1 (Pro Vector Engine, Медиа и Контроллер узлов)\n"
            "Разработка: MindsMap Team\n\n"
            "Профессиональный конструктор интерактивных схем: узел «Магнитола» "
            "для воспроизведения аудио и узел «Контроллер» для управления "
            "состоянием связанных узлов в реальном времени."
        )
        messagebox.showinfo("О программе", about_text)

    def setup_context_menus(self):
        self.bg_menu = tk.Menu(self, tearoff=0)
        self.bg_menu.add_command(label="Текстовый блок", command=lambda: self.create_node("Текст"))
        self.bg_menu.add_command(label="Веб-страница (HTML)", command=lambda: self.create_node("Страница", initial="<h1>Заголовок</h1>\nТекст..."))
        self.bg_menu.add_command(label="Фрагмент кода", command=lambda: self.create_node("Код", initial="python\n# code"))
        self.bg_menu.add_command(label="Ярлык (Ссылка)", command=lambda: self.create_node("Ссылка", initial="https://"))
        self.bg_menu.add_command(label="Часы", command=lambda: self.create_node("Часы"))
        self.bg_menu.add_command(label="Магнитола", command=lambda: self.create_node("Магнитола"))
        self.bg_menu.add_command(label="Контроллер узлов", command=lambda: self.create_node("Контроллер"))
        
        ins_menu = tk.Menu(self.bg_menu, tearoff=0)
        ins_menu.add_command(label="Список", command=lambda: self.create_node("Список", initial="Пункт 1\nПункт 2"))
        ins_menu.add_command(label="Таблица (Простая)", command=lambda: self.create_node("Таблица", initial="Col1, Col2\nVal1, Val2"))
        ins_menu.add_command(label="Прогресс бар", command=lambda: self.create_node("Прогресс бар", initial="Готовность | 50"))
        ins_menu.add_command(label="Математическая функция", command=lambda: self.create_node("Функция", initial="sum({Cars}.Price) + 10"))
        ins_menu.add_command(label="Диаграмма (Bar)", command=lambda: self.create_node("Диаграмма", initial="Январь: 120\nФевраль: 80\nМарт: 95"))
        ins_menu.add_command(label="Секторная диаграмма (Pie)", command=lambda: self.create_node("Секторная диаграмма", initial="Альфа: 40\nБета: 35\nГамма: 25"))
        
        dat_menu = tk.Menu(self.bg_menu, tearoff=0)
        dat_menu.add_command(label="Сводка (Таблица данных)", command=lambda: self.create_node("Сводка", initial="Cars\nModel, Price\nBMW, 5000\nAudi, {BMW}.Price*0.8"))
        dat_menu.add_command(label="Переменная (Variable)", command=lambda: self.create_node("Переменная", initial="X = 10\nValue = Привет"))
        
        ina_menu = tk.Menu(self.bg_menu, tearoff=0)
        ina_menu.add_command(label="Регулятор (Slider/List)", command=lambda: self.create_node("Регулятор", initial="Speed = 50\n0, 100, 1"))
        ina_menu.add_command(label="Переключатель (Чекбокс)", command=lambda: self.create_node("Переключатель", initial="Сделать задачу"))


        self.bg_menu.add_cascade(label="Интерактив...", menu=ina_menu)
        self.bg_menu.add_cascade(label="Данные&Среда...", menu=dat_menu)
        self.bg_menu.add_cascade(label="Вставка...", menu=ins_menu)
        
        self.bg_menu.add_separator()
        self.bg_menu.add_command(label="Добавить Изображение", command=self.create_image_node)
        self.bg_menu.add_command(label="Вставить (Ctrl+V)", command=self.on_paste)

        self.node_menu = tk.Menu(self, tearoff=0, bg="#FFFFFF", activebackground="#EAEAEA")
        self.node_menu.add_command(label="Редактировать текст", command=self.edit_node)
        self.node_menu.add_command(label="Свойства оформления", command=self.edit_node_properties)
        self.node_menu.add_command(label="Провести связь", command=self.start_connection)
        self.node_menu.add_separator()
        self.node_menu.add_command(label="Копировать", command=self.on_copy)
        self.node_menu.add_command(label="Вырезать", command=self.on_cut)
        self.node_menu.add_command(label="Дублировать", command=self.duplicate_node)
        self.node_menu.add_separator()
        self.node_menu.add_command(label="Сбросить масштаб", command=self.reset_node_scale)
        self.node_menu.add_command(label="Удалить", command=self.delete_node)

        self.edge_menu = tk.Menu(self, tearoff=0, bg="#FFFFFF", activebackground="#EAEAEA")
        self.edge_menu.add_command(label="Направление: A -> B", command=lambda: self.set_edge_dir(1))
        self.edge_menu.add_command(label="Направление: A <-> B", command=lambda: self.set_edge_dir(2))
        self.edge_menu.add_command(label="Направление: A - B", command=lambda: self.set_edge_dir(0))
        self.edge_menu.add_separator()
        self.edge_menu.add_command(label="Удалить связь", command=self.delete_node)

    def set_edge_dir(self, direction):
        if getattr(self, 'selected_edge', None) is not None:
            if len(self.edges[self.selected_edge]) > 2:
                self.edges[self.selected_edge][2] = direction
            else:
                self.edges[self.selected_edge].append(direction)
            self.save_state()
            self.render()

    def get_current_vars(self):
        """Парсинг и компиляция значений переменных из схемы в единый контекст вычислений."""
        raw_vars = {}
        raw_tables = {}

        for n in self.nodes.values():
            n_type = n["type"]
            if n_type in ("Переменная", "Регулятор"):
                lines = n["content"].split("\n")
                if n_type == "Регулятор" and lines:
                    lines = [lines[0]]
                for line in lines:
                    if "=" in line:
                        k, v = line.split("=", 1)
                        raw_vars[k.strip()] = v.strip()
            elif n_type == "Сводка":
                lines = [l.strip() for l in n["content"].split("\n") if l.strip()]
                if len(lines) >= 2:
                    t_name = lines[0]
                    headers = [h.strip() for h in lines[1].split(",")]
                    raw_tables[t_name] = {"headers": headers, "rows": lines[2:]}

        context = {}
        
        def eval_cell(expr_str):
            if '{' not in str(expr_str):
                try:
                    f_val = float(expr_str)
                    return int(f_val) if f_val.is_integer() else f_val
                except ValueError:
                    return expr_str

            math_expr = RE_INTERPOLATION_BRACKETS.sub(r"(\1)", str(expr_str))
            math_expr = math_expr.replace('×', '*').replace('÷', '/').replace('^', '**')
            math_expr = math_expr.replace('²', '**2').replace('³', '**3')
            math_expr = math_expr.replace('√(', 'sqrt(')
            math_expr = RE_MATH_SQRT.sub(r'sqrt(\1)', math_expr)
            math_expr = math_expr.replace('π', 'pi').replace('∞', 'inf')
            
            try:
                res = eval(math_expr, {"__builtins__": None}, {**SAFE_MATH_DICT, **context})
                if isinstance(res, float) and res.is_integer(): 
                    return int(res)
                if isinstance(res, float): 
                    return round(res, 6)
                return res
            except Exception:
                pass
                
            def replacer(match):
                inner = match.group(1).strip()
                chain = match.group(2)
                full_expr = inner + chain
                
                try:
                    res = eval(full_expr, {"__builtins__": None}, {**SAFE_MATH_DICT, **context})
                    if isinstance(res, float) and res.is_integer(): 
                        return str(int(res))
                    if isinstance(res, float): 
                        return str(round(res, 6))
                    return str(res)
                except Exception:
                    if inner in context and not chain: 
                        return str(context[inner])
                    return match.group(0)
                    
            res_str = RE_CHAIN_ACCESS.sub(replacer, str(expr_str))
            try:
                f_val = float(res_str)
                return int(f_val) if f_val.is_integer() else f_val
            except ValueError:
                return res_str

        changed = True
        iterations = 0
        
        while changed and iterations < 12:
            changed = False
            
            for k, expr in raw_vars.items():
                val = eval_cell(expr)
                if k not in context or context[k] != val:
                    context[k] = val
                    changed = True
                    
            for t_name, t_data in raw_tables.items():
                headers = t_data["headers"]
                parsed_rows = []
                for row_str in t_data["rows"]:
                    row_vals = split_csv_line(row_str)
                    row_dict = {}
                    for i, h in enumerate(headers):
                        cell_expr = row_vals[i] if i < len(row_vals) else ""
                        row_dict[h] = eval_cell(cell_expr)
                    parsed_rows.append(row_dict)
                
                new_table = DataTable(t_name, headers, parsed_rows)
                if t_name not in context or context[t_name] != new_table:
                    context[t_name] = new_table
                    changed = True
                    
            iterations += 1

        return context

    def process_content(self, text, vars_dict):
        """Интерполяция строк с учетом объектных обращений и математических расчетов."""
        if not text or '{' not in str(text): 
            return text
        
        def replacer(match):
            inner = match.group(1).strip()
            chain = match.group(2)
            
            full_expr = inner + chain
            res, _, err = evaluate_math_expression(full_expr, vars_dict)
            
            if not err and res is not None:
                if isinstance(res, float) and res.is_integer(): 
                    return str(int(res))
                return str(res)
                
            if inner in vars_dict and not chain:
                val = vars_dict[inner]
                if isinstance(val, float) and val.is_integer(): 
                    return str(int(val))
                return str(val)
                
            return match.group(0)
            
        return RE_CHAIN_ACCESS.sub(replacer, str(text))

    def toggle_view_mode(self, from_key=False):
        if from_key:
            self.view_mode.set(not self.view_mode.get())
            
        if self.view_mode.get():
            self.update_status("Включен режим просмотра (Узлы защищены от сдвигов)")
            if self.selected_node:
                self.set_node_selected(self.selected_node, False)
                prev, self.selected_node = self.selected_node, None
                self.canvas.delete(prev)
                if prev in self.nodes: 
                    self.draw_node(prev, self.nodes[prev])
            if self.connecting_from:
                self.connecting_from = None
                self.canvas.delete("temp_edge")
        else:
            self.update_status("Режим редактирования")

    def show_help(self):
        help_win = tk.Toplevel(self)
        help_win.title("Справка по горячим клавишам")
        help_win.geometry("560x580")
        help_win.configure(bg="#F3F3F3")
        help_win.transient(self)
        
        tk.Label(help_win, text="Управление и горячие клавиши", font=("Segoe UI", 12, "bold"), background="#F3F3F3", fg="#1C1C1C").pack(pady=15)
        
        frame = tk.Frame(help_win, bg="#FFFFFF", highlightbackground="#E5E5E5", highlightthickness=1)
        frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=5)
        
        shortcuts = [
            ("F3", "Переключение режима просмотра"),
            ("Клик на чекбоксе", "Переключение логического состояния"),
            ("Клик на связи", "Выделение линии ребра"),
            ("Двойной клик ЛКМ", "Редактирование текста"),
            ("ПКМ", "Контекстное меню элементов"),
            ("Пробел + ЛКМ", "Перемещение по бесконечному холсту"),
            ("Ctrl + Колесико", "Масштабирование к курсору"),
            ("F2", "Быстрый редактор узла"),
            ("Ctrl+C / Ctrl+X / Ctrl+V", "Копировать / Вырезать / Вставить"),
            ("Ctrl+D", "Быстрое дублирование узла"),
            ("Delete", "Удалить выделенный узел или связь"),
            ("Escape", "Отменить создание связи или сбросить выделение"),
        ]
        
        tree = ttk.Treeview(frame, columns=("Key", "Desc"), show="headings", height=15)
        tree.heading("Key", text="Клавиша / Действие")
        tree.heading("Desc", text="Описание")
        tree.column("Key", width=180, anchor=tk.W)
        tree.column("Desc", width=300, anchor=tk.W)
        
        for k, d in shortcuts:
            tree.insert("", tk.END, values=(k, d))
            
        tree.pack(fill=tk.BOTH, expand=True)
        ttk.Button(help_win, text="Закрыть", command=help_win.destroy).pack(pady=15)

    def align_all_to_grid(self):
        if self.view_mode.get(): 
            return
        for n in self.nodes.values():
            n["x"] = round(n["x"] / self.grid_size) * self.grid_size
            n["y"] = round(n["y"] / self.grid_size) * self.grid_size
        self.save_state()
        self.render()
        self.update_navigator_list()
        self.update_status("Узлы выровнены по сетке")

    def clear_canvas(self):
        if self.view_mode.get(): 
            return
        if messagebox.askyesno("Очистить холст", "Вы действительно хотите удалить все элементы схемы?"):
            self.nodes.clear()
            self.edges.clear()
            self.selected_node = None
            self.selected_edge = None
            self.connecting_from = None
            self.animated_items.clear()
            self.save_state()
            self.render()
            self.update_navigator_list()
            self.update_status("Холст полностью очищен")
            
    def on_copy(self, event=None):
        if self.selected_node and self.selected_node in self.nodes:
            self.internal_clipboard = copy.deepcopy(self.nodes[self.selected_node])
            self.update_status("Узел успешно скопирован")

    def on_cut(self, event=None):
        if self.view_mode.get(): 
            return
        if self.selected_node and self.selected_node in self.nodes:
            self.internal_clipboard = copy.deepcopy(self.nodes[self.selected_node])
            self.delete_node()
            self.update_status("Узел вырезан")

    def update_status(self, text):
        self.status_bar.config(text=text)

    def _get_controller_targets(self, controller_id):
        seen = []
        for e in self.edges:
            other = None
            if e[0] == controller_id and e[1] in self.nodes:
                other = e[1]
            elif e[1] == controller_id and e[0] in self.nodes:
                other = e[0]
            if other and other not in [t[0] for t in seen]:
                seen.append((other, self.nodes[other]))
        return seen

    def _controller_state_glyph(self, t_node):
        t_type = t_node["type"]
        if t_type == "Часы":
            return ("⏸" if not t_node.get("is_running", True) else "▶", "#EF4444")
        if t_type == "Магнитола":
            return ("▶" if t_node.get("is_playing", False) else "⏸", "#0EA5E9")
        if t_type == "Переключатель":
            state = t_node.get("state", 0)
            return (["○", "◐", "●"][state % 3], "#14B8A6")
        return ("•", "#9CA3AF")

    def _controller_toggle_target(self, t_id, t_node):
        t_type = t_node["type"]
        if t_type == "Часы":
            t_node["is_running"] = not t_node.get("is_running", True)
            t_node["last_update"] = time.time()
        elif t_type == "Магнитола":
            self._magnitola_toggle_play(t_id, t_node)
        elif t_type == "Переключатель":
            t_node["state"] = (t_node.get("state", 0) + 1) % 3
        else:
            return False
        return True

    def _magnitola_stop_playback(self):
        if HAS_WINSOUND:
            try:
                winsound.PlaySound(None, winsound.SND_ASYNC)
            except Exception:
                pass

    def _magnitola_play_track(self, node_id, n):
        playlist = n.get("playlist", [])
        if not playlist:
            self.update_status("Плейлист пуст — добавьте треки кнопкой «+»")
            return
        idx = n.get("track_idx", 0) % len(playlist)
        n["track_idx"] = idx
        filepath = playlist[idx]
        self._magnitola_stop_playback()
        played_inline = False
        if HAS_WINSOUND and filepath.lower().endswith(".wav") and os.path.isfile(filepath):
            try:
                winsound.PlaySound(filepath, winsound.SND_FILENAME | winsound.SND_ASYNC)
                played_inline = True
            except Exception:
                played_inline = False
        if not played_inline:
            try:
                if hasattr(os, 'startfile'):
                    os.startfile(filepath)
                else:
                    import subprocess, sys
                    opener = "open" if sys.platform == "darwin" else "xdg-open"
                    subprocess.Popen([opener, filepath])
            except Exception as e:
                self.update_status(f"Не удалось воспроизвести файл: {e}")
                return
        n["is_playing"] = True
        n["elapsed"] = 0.0
        n["play_started_at"] = time.time()
        self.update_status(f"Воспроизведение: {os.path.basename(filepath)}")

    def _magnitola_toggle_play(self, node_id, n):
        if n.get("is_playing", False):
            n["is_playing"] = False
            n["play_started_at"] = None
            self._magnitola_stop_playback()
            self.update_status("Магнитола остановлена")
        else:
            self._magnitola_play_track(node_id, n)

    def _magnitola_shift_track(self, node_id, n, delta):
        playlist = n.get("playlist", [])
        if not playlist:
            return
        n["track_idx"] = (n.get("track_idx", 0) + delta) % len(playlist)
        if n.get("is_playing", False):
            self._magnitola_play_track(node_id, n)

    def _magnitola_add_tracks(self, node_id, n):
        paths = filedialog.askopenfilenames(title="Добавить треки", filetypes=[("Аудиофайлы", "*.wav *.mp3 *.ogg *.flac *.wma *.m4a *.aac"), ("Все файлы", "*.*")])
        if paths:
            n.setdefault("playlist", []).extend(paths)
            self.update_status(f"Добавлено треков: {len(paths)}")

    def update_animations(self):
        current_real_time = time.time()
        for node_id, n in self.nodes.items():
            if n["type"] == "Часы":
                is_running = n.get("is_running", True)
                last_upd = n.get("last_update", current_real_time)
                delta = current_real_time - last_upd
                n["last_update"] = current_real_time
                if is_running:
                    n["clock_time"] = n.get("clock_time", current_real_time) + delta
                try:
                    dt = datetime.datetime.fromtimestamp(n.get("clock_time", current_real_time))
                    self.canvas.itemconfig(f"{node_id}_time", text=dt.strftime("%H:%M:%S"))
                    self.canvas.itemconfig(f"{node_id}_date", text=dt.strftime("%d.%m.%Y"))
                except tk.TclError:
                    pass
            elif n["type"] == "Магнитола" and n.get("is_playing", False):
                started = n.get("play_started_at")
                if started:
                    n["elapsed"] = current_real_time - started
                playlist = n.get("playlist", [])
                idx = n.get("track_idx", 0)
                pos_str = f"{int(n['elapsed'])//60:02d}:{int(n['elapsed'])%60:02d}"
                try:
                    self.canvas.itemconfig(f"{node_id}_pos", text=f"Трек {idx+1 if playlist else 0}/{len(playlist)}   {pos_str}")
                except tk.TclError:
                    pass
            elif n["type"] == "Контроллер":
                if self._get_controller_targets(node_id):
                    try:
                        self.canvas.delete(node_id)
                        self.draw_node(node_id, n)
                        if self.selected_node == node_id:
                            self.set_node_selected(node_id, True)
                    except tk.TclError:
                        pass

        active_files = set(data["filepath"] for data in self.animated_items.values())
        for fp in active_files:
            self.anim_ticks[fp] = self.anim_ticks.get(fp, 0) + 1

        for node_id, data in list(self.animated_items.items()):
            cache = self.image_cache.get(data.get("cache_key"))
            if cache and isinstance(cache, dict) and cache.get("animated"):
                frames = cache["frames"]
                if not frames: 
                    continue
                
                idx = self.anim_ticks[data["filepath"]] % len(frames)
                if frames[idx] is None:
                    try:
                        source_data = self.source_image_cache[data["filepath"]]
                        f_copy = source_data["frames"][idx].copy()
                        f_copy.thumbnail((cache["target_w"], cache["target_h"]), Image.Resampling.LANCZOS)
                        frames[idx] = ImageTk.PhotoImage(f_copy)
                    except Exception:
                        continue
                try:
                    self.canvas.itemconfig(data["item_id"], image=frames[idx])
                except tk.TclError:
                    pass
                    
        self.after(80, self.update_animations)

    def screen_to_world(self, sx, sy):
        wx = (sx - self.offset_x) / self.zoom_level
        wy = (sy - self.offset_y) / self.zoom_level
        return wx, wy

    def world_to_screen(self, wx, wy):
        sx = wx * self.zoom_level + self.offset_x
        sy = wy * self.zoom_level + self.offset_y
        return sx, sy

    def schedule_render(self):
        if self._render_timer:
            self.after_cancel(self._render_timer)
        self._render_timer = self.after(10, self.render)

    def on_mouse_wheel(self, event):
        factor = 1.1 if event.delta > 0 else 0.9
        self.do_zoom(factor, event.x, event.y)

    def do_zoom(self, factor, x=None, y=None):
        if x is None: 
            x = self.canvas.winfo_width() / 2
        if y is None: 
            y = self.canvas.winfo_height() / 2

        old_zoom = self.zoom_level
        self.zoom_level *= factor
        self.zoom_level = max(0.1, min(self.zoom_level, 5.0))
        
        actual_factor = self.zoom_level / old_zoom
        self.offset_x = x - (x - self.offset_x) * actual_factor
        self.offset_y = y - (y - self.offset_y) * actual_factor

        self.zoom_label.config(text=f"{int(self.zoom_level * 100)}%")
        self.schedule_render()

    def reset_zoom(self):
        center_x = self.canvas.winfo_width() / 2
        center_y = self.canvas.winfo_height() / 2
        wx, wy = self.screen_to_world(center_x, center_y)
        
        self.zoom_level = 1.0
        self.offset_x = center_x - wx
        self.offset_y = center_y - wy
        
        self.zoom_label.config(text="100%")
        self.render()

    def pan_by(self, dx, dy):
        self.offset_x += dx
        self.offset_y += dy
        self.canvas.move("node", dx, dy)
        self.canvas.move("edge", dx, dy)
        self.canvas.move("temp_edge", dx, dy)
        self.draw_grid()

    def on_paste(self, event=None):
        if self.view_mode.get(): 
            return
        
        x, y = self.mouse_pos
        world_x, world_y = self.screen_to_world(x, y)
        
        if self.internal_clipboard:
            new_node = copy.deepcopy(self.internal_clipboard)
            self.node_counter += 1
            new_id = f"node_{self.node_counter}"
            new_node["id"] = new_id
            new_node["x"] = world_x
            new_node["y"] = world_y
            
            if new_node["type"] == "Часы":
                new_node["last_update"] = time.time()
            
            if self.snap_to_grid.get():
                new_node["x"] = round(new_node["x"] / self.grid_size) * self.grid_size
                new_node["y"] = round(new_node["y"] / self.grid_size) * self.grid_size
                
            self.nodes[new_id] = new_node
            
            if self.selected_node:
                self.set_node_selected(self.selected_node, False)
            self.selected_node = new_id
            self.selected_edge = None
            self.save_state()
            
            if new_node["type"] in ["Переменная", "Регулятор", "Сводка"]:
                self.render()
            else:
                self.draw_node(new_id, new_node)
                self.set_node_selected(new_id, True)
                
            self.update_navigator_list()
            self.update_status("Элемент вставлен")
            return
        
        if HAS_PIL:
            try:
                img = ImageGrab.grabclipboard()
                if img is not None:
                    if isinstance(img, list):
                        for f in img:
                            if f.lower().endswith(('.png', '.jpg', '.jpeg', '.gif', '.webp')):
                                self.create_image_node_from_file(f, world_x, world_y)
                                world_x += 30
                    else:
                        temp_dir = tempfile.gettempdir()
                        temp_file = os.path.join(temp_dir, f"cb_image_{self.node_counter}.png")
                        img.save(temp_file, 'PNG')
                        self.create_image_node_from_file(temp_file, world_x, world_y, is_temp=True)
                    self.update_navigator_list()
                    self.update_status("Изображение вставлено")
                    return
            except Exception:
                pass

        try:
            text = self.clipboard_get()
            if text:
                n_type = "Код" if "{" in text or "def " in text or ";" in text else "Текст"
                initial = f"text\n{text}" if n_type == "Код" else text
                self.create_node(n_type, initial=initial, at_x=world_x, at_y=world_y)
                self.update_status("Текст импортирован из буфера")
        except tk.TclError:
            pass

    def on_mouse_move(self, event):
        self.mouse_pos = (event.x, event.y)
        if self.connecting_from:
            self.draw_temp_connection()

    def draw_temp_connection(self):
        self.canvas.delete("temp_edge")
        if self.connecting_from and self.connecting_from in self.nodes:
            n = self.nodes[self.connecting_from]
            s = n.get("scale", 1.0)
            x1, y1 = self.world_to_screen(n["x"] + (n["w"]*s)/2, n["y"] + (n["h"]*s)/2)
            self.canvas.create_line(x1, y1, self.mouse_pos[0], self.mouse_pos[1], fill="#9CA3AF", dash=(4, 2), width=2, tags="temp_edge")

    def on_space_down(self, event):
        self.space_pressed = True
        self.canvas.config(cursor="fleur")

    def on_space_up(self, event):
        self.space_pressed = False
        self.canvas.config(cursor="")

    def on_escape(self, event):
        if self.view_mode.get(): 
            return
        
        if self.connecting_from:
            self.connecting_from = None
            self.canvas.delete("temp_edge")
            self.update_status("Связывание отменено")
        elif self.selected_node or self.selected_edge is not None:
            if self.selected_node:
                self.set_node_selected(self.selected_node, False)
            self.selected_node = None
            self.selected_edge = None
            self.render()
            self.update_status("Выделение очищено")

    def on_pan_start(self, event):
        self.pan_start_x = event.x
        self.pan_start_y = event.y

    def on_pan_drag(self, event):
        dx = event.x - self.pan_start_x
        dy = event.y - self.pan_start_y
        self.offset_x += dx
        self.offset_y += dy
        self.pan_start_x = event.x
        self.pan_start_y = event.y

        self.canvas.move("node", dx, dy)
        self.canvas.move("edge", dx, dy)
        self.canvas.move("temp_edge", dx, dy)
        self.draw_grid()

    def get_node_at(self, sx, sy):
        wx, wy = self.screen_to_world(sx, sy)
        for node_id in reversed(list(self.nodes.keys())):
            n = self.nodes[node_id]
            scale = n.get("scale", 1.0)
            if n["x"] <= wx <= n["x"] + n["w"] * scale and n["y"] <= wy <= n["y"] + n["h"] * scale:
                return node_id
        return None

    def _parse_slider_config(self, lines):
        is_numeric = True
        range_vals = [0.0, 100.0, 1.0]
        list_vals = []
        
        if len(lines) > 1:
            parts = [p.strip() for p in lines[1].split(",") if p.strip()]
            try:
                range_vals = [float(p) for p in parts]
                if len(range_vals) == 2: 
                    range_vals.append(1.0)
                elif len(range_vals) < 2: 
                    range_vals = [0.0, max(100.0, range_vals[0] if range_vals else 100.0), 1.0]
            except ValueError:
                is_numeric = False
                list_vals = parts
                
        return is_numeric, range_vals, list_vals

    def _update_knob_val(self, n, local_x, local_y, range_vals):
        lines = n["content"].split("\n")
        if not lines or "=" not in lines[0]: 
            return
        var_name = lines[0].split("=")[0].strip()
        
        min_v, max_v, step_v = range_vals[0], range_vals[1], range_vals[2]
        if max_v < min_v: 
            max_v = min_v
        
        knob_cx = n["w"] / 2
        # Адаптивный расчет центра регулятора по высоте узла
        available_knob_h = n["h"] - 26 - 15
        knob_cy = (26 + 10) + available_knob_h / 2
        
        dx = local_x - knob_cx
        dy = local_y - knob_cy
        
        deg = math.degrees(math.atan2(dy, dx))
        relative_deg = (deg - 135) % 360
        
        if relative_deg > 270:
            if relative_deg > 315: 
                ratio = 0.0 
            else: 
                ratio = 1.0 
        else:
            ratio = relative_deg / 270.0
            
        ratio = max(0.0, min(1.0, ratio))
        raw_val = min_v + ratio * (max_v - min_v)
        
        if step_v > 0:
            steps = round((raw_val - min_v) / step_v)
            snapped_val = min_v + steps * step_v
            snapped_val = min(max_v, snapped_val)
        else:
            snapped_val = raw_val
            
        if step_v.is_integer() and min_v.is_integer():
            final_val = int(snapped_val)
        else:
            final_val = round(snapped_val, 4)
            if final_val.is_integer(): 
                final_val = int(final_val)
            
        lines[0] = f"{var_name} = {final_val}"
        n["content"] = "\n".join(lines)

    def fit_text_to_box(self, text, font_family, max_width, max_height, zs, is_code=False):
        """
        Вписывает текст в заданные рамки по ширине и высоте с динамическим уменьшением шрифта.
        При необходимости усекает текст и добавляет троеточие.
        """
        import textwrap
        if not text:
            return ([], 10)
            
        paragraphs = text.split('\n')
        # Пытаемся подобрать размер шрифта от 10 до 6
        for font_size in range(10, 5, -1):
            char_width = font_size * (0.6 if is_code else 0.45) * zs
            chars_per_line = max(5, int(max_width / char_width))
            
            wrapped_lines = []
            for p in paragraphs:
                if not p.strip():
                    wrapped_lines.append("")
                    continue
                p_lines = textwrap.wrap(p, width=chars_per_line)
                wrapped_lines.extend(p_lines)
                
            line_height = font_size * 1.35 * zs
            total_height = len(wrapped_lines) * line_height
            
            if total_height <= max_height:
                return (wrapped_lines, font_size)
                
        # Если даже на минимальном размере шрифта (6) текст переполняет рамку, усекаем его
        font_size = 6
        char_width = font_size * (0.6 if is_code else 0.45) * zs
        chars_per_line = max(5, int(max_width / char_width))
        
        wrapped_lines = []
        for p in paragraphs:
            if not p.strip():
                wrapped_lines.append("")
                continue
            p_lines = textwrap.wrap(p, width=chars_per_line)
            wrapped_lines.extend(p_lines)
            
        line_height = font_size * 1.35 * zs
        max_lines = int(max_height / line_height)
        
        if max_lines <= 0:
            return ([], font_size)
            
        if len(wrapped_lines) > max_lines:
            truncated = wrapped_lines[:max_lines]
            if truncated:
                last_line = truncated[-1]
                if len(last_line) > 3:
                    truncated[-1] = last_line[:-3] + "..."
                else:
                    truncated[-1] = "..."
            return (truncated, font_size)
            
        return (wrapped_lines, font_size)

    def on_lmb_down(self, event):
        if self.view_mode.get() or self.space_pressed:
            self.on_pan_start(event)
            return

        clicked_items = self.canvas.find_withtag("current")
        clicked_edge_idx = None
        if clicked_items:
            tags = self.canvas.gettags(clicked_items[0])
            if "resize_handle" in tags:
                for t in tags:
                    if t.startswith("node_"):
                        self.resizing_node = t
                        self.update_status("Свободное изменение пропорций узла...")
                        return
            elif "edge" in tags:
                for t in tags:
                    if t.startswith("edge_idx_"):
                        clicked_edge_idx = int(t.split("_")[-1])

        node_id = self.get_node_at(event.x, event.y)
        
        if self.connecting_from:
            if node_id and node_id != self.connecting_from:
                exists = any(e[0] == self.connecting_from and e[1] == node_id for e in self.edges)
                if not exists:
                    self.edges.append([self.connecting_from, node_id, 1]) 
                    self.save_state()
                    self.update_status("Связь установлена")
            self.connecting_from = None
            self.canvas.delete("temp_edge")
            self.draw_edges()
            return

        interacted = False
        re_render_all = False
        
        if node_id and not self.view_mode.get():
            n = self.nodes[node_id]
            sx, sy = self.world_to_screen(n["x"], n["y"])
            zs = self.zoom_level * n.get("scale", 1.0)
            
            local_x = (event.x - sx) / zs
            local_y = (event.y - sy) / zs
            
            if not n.get("hide_content", False):
                if n["type"] == "Регулятор":
                    lines = n["content"].split("\n")
                    if len(lines) > 0 and "=" in lines[0]:
                        var_name, var_val = [p.strip() for p in lines[0].split("=", 1)]
                        is_numeric, range_vals, list_vals = self._parse_slider_config(lines)

                        pad_y_local = 26 + 10 
                        if is_numeric:
                            knob_cx_local = n["w"] / 2
                            # Адаптивный расчет центра и радиуса для попадания мыши
                            available_knob_h_local = n["h"] - 26 - 15
                            knob_cy_local = pad_y_local + available_knob_h_local / 2
                            knob_r_local = min(35, available_knob_h_local * 0.4, n["w"] * 0.35)
                            
                            dist = math.hypot(local_x - knob_cx_local, local_y - knob_cy_local)
                            if dist <= knob_r_local * 1.3: 
                                self.active_slider = node_id
                                self._update_knob_val(n, local_x, local_y, range_vals)
                                interacted = True
                                re_render_all = True
                        else:
                            bar_y_local = pad_y_local + 25
                            if bar_y_local <= local_y <= bar_y_local + 25:
                                btn_w = 25
                                if 15 <= local_x <= 15 + btn_w:
                                    if var_val in list_vals:
                                        idx = list_vals.index(var_val)
                                        new_val = list_vals[(idx - 1) % len(list_vals)]
                                    else:
                                        new_val = list_vals[0] if list_vals else var_val
                                    lines[0] = f"{var_name} = {new_val}"
                                    n["content"] = "\n".join(lines)
                                    interacted = True
                                    re_render_all = True
                                elif n["w"] - 15 - btn_w <= local_x <= n["w"] - 15:
                                    if var_val in list_vals:
                                        idx = list_vals.index(var_val)
                                        new_val = list_vals[(idx + 1) % len(list_vals)]
                                    else:
                                        new_val = list_vals[0] if list_vals else var_val
                                    lines[0] = f"{var_name} = {new_val}"
                                    n["content"] = "\n".join(lines)
                                    interacted = True
                                    re_render_all = True
                                    
                elif n["type"] == "Переключатель":
                    if local_y > 30 and local_x < 50:
                        n["state"] = (n.get("state", 0) + 1) % 3
                        interacted = True
                        
                elif n["type"] == "Ссылка":
                    if local_x >= n["w"] - 35 and local_y >= 30:
                        raw_path = n["content"].strip()
                        path = self.process_content(raw_path, getattr(self, '_cached_vars', {})).strip()
                        if path:
                            try:
                                if path.startswith("http://") or path.startswith("https://") or path.startswith("www."):
                                    webbrowser.open(path)
                                else:
                                    if hasattr(os, 'startfile'): 
                                        os.startfile(path)
                                    else:
                                        import subprocess, sys
                                        opener = "open" if sys.platform == "darwin" else "xdg-open"
                                        subprocess.call([opener, path])
                            except Exception as e:
                                print(f"Ошибка перехода по ссылке: {e}")
                        interacted = True
                        
                elif n["type"] == "Список":
                    if local_y > 36:
                        # Адаптивный расчет высоты шага списка
                        f_size_est = max(6, min(10, int((n["h"] - 36) / (len(display_content.split('\n')) * 1.5)) if len(display_content.split('\n')) > 1 else 10))
                        item_idx = int((local_y - 36) // (f_size_est * 1.5))
                        display_content = self.process_content(n["content"], getattr(self, '_cached_vars', {}))
                        items = [it for it in display_content.split("\n") if it.strip()]
                        if 0 <= item_idx < len(items) and local_x < n["w"] - 15:
                            checked = n.get("checked_items", [])
                            if item_idx in checked: 
                                checked.remove(item_idx)
                            else: 
                                checked.append(item_idx)
                            n["checked_items"] = checked
                            interacted = True

                elif n["type"] == "Магнитола":
                    btn_y_local = n["h"] - 30
                    if n["w"] - 30 <= local_x <= n["w"] - 2 and 24 <= local_y <= 50:
                        self._magnitola_add_tracks(node_id, n)
                        interacted = True
                    elif btn_y_local - 14 <= local_y <= btn_y_local + 14:
                        if n["w"]*0.28 - 16 <= local_x <= n["w"]*0.28 + 16:
                            self._magnitola_shift_track(node_id, n, -1)
                            interacted = True
                        elif n["w"]*0.50 - 18 <= local_x <= n["w"]*0.50 + 18:
                            self._magnitola_toggle_play(node_id, n)
                            interacted = True
                        elif n["w"]*0.72 - 16 <= local_x <= n["w"]*0.72 + 16:
                            self._magnitola_shift_track(node_id, n, 1)
                            interacted = True

                elif n["type"] == "Контроллер":
                    targets = self._get_controller_targets(node_id)
                    row_h_local = 28
                    if local_y > 36 and targets:
                        row_idx = int((local_y - 36) / row_h_local)
                        if 0 <= row_idx < len(targets):
                            t_id, t_node = targets[row_idx]
                            if self._controller_toggle_target(t_id, t_node):
                                interacted = True
                                re_render_all = True
                        
            if interacted:
                if not self.active_slider:
                    self.save_state()
                if re_render_all:
                    self.render()
                else:
                    self.canvas.delete(node_id)
                    self.draw_node(node_id, n)

        if node_id:
            self.selected_edge = None
            if self.selected_node and self.selected_node != node_id:
                self.set_node_selected(self.selected_node, False)
                prev = self.selected_node
                self.selected_node = node_id
                if prev in self.nodes: 
                    self.canvas.delete(prev)
                    self.draw_node(prev, self.nodes[prev])
                    
            self.selected_node = node_id
            n = self.nodes[self.selected_node]
            wx, wy = self.screen_to_world(event.x, event.y)
            self.drag_data = {"x": wx - n["x"], "y": wy - n["y"]}
            
            self.nodes[self.selected_node] = self.nodes.pop(self.selected_node)
            self.canvas.tag_raise(self.selected_node)
            
            if not interacted:
                self.canvas.delete(self.selected_node)
                self.draw_node(self.selected_node, n)
            
            self.set_node_selected(self.selected_node, True)
            self.render() 
            
        elif clicked_edge_idx is not None:
            if self.selected_node:
                self.set_node_selected(self.selected_node, False)
                self.selected_node = None
                
            self.selected_edge = clicked_edge_idx
            self.render()
            self.update_status("Связь выделена")
            
        else:
            if self.selected_node:
                self.set_node_selected(self.selected_node, False)
                self.selected_node = None
                
            self.selected_edge = None
            self.panning = True
            self.pan_start_x = event.x
            self.pan_start_y = event.y
            wx, wy = self.screen_to_world(event.x, event.y)
            self.render() 
            self.update_status(f"Координаты: X={int(wx)}, Y={int(wy)}")

    def on_double_click(self, event):
        if self.view_mode.get(): 
            return
        node_id = self.get_node_at(event.x, event.y)
        if node_id:
            if self.selected_node and self.selected_node != node_id:
                self.set_node_selected(self.selected_node, False)
            self.selected_node = node_id
            self.set_node_selected(self.selected_node, True)
            self.edit_node()

    def on_lmb_drag(self, event):
        if self.view_mode.get() or self.space_pressed or getattr(self, 'panning', False):
            self.on_pan_drag(event)
            return
            
        if getattr(self, 'active_slider', None):
            n = self.nodes[self.active_slider]
            zs = self.zoom_level * n.get("scale", 1.0)
            sx, sy = self.world_to_screen(n["x"], n["y"])
            local_x = (event.x - sx) / zs
            local_y = (event.y - sy) / zs
            
            lines = n["content"].split("\n")
            if len(lines) > 1:
                is_numeric, range_vals, list_vals = self._parse_slider_config(lines)
                if is_numeric:
                    self._update_knob_val(n, local_x, local_y, range_vals)
                    self.render() 
            return

        if self.resizing_node:
            n = self.nodes[self.resizing_node]
            wx, wy = self.screen_to_world(event.x, event.y)
            
            new_w = max(60, wx - n["x"])
            new_h = max(45, wy - n["y"])
            
            if n.get("lock_aspect_ratio", False):
                ratio = n.get("aspect_ratio", 1.33)
                new_h = new_w / ratio
                
            n["w"] = new_w
            n["h"] = new_h
            n["scale"] = 1.0 
            
            self.canvas.delete(self.resizing_node)
            self.draw_node(self.resizing_node, n)
            self.draw_edges()
            return

        if self.selected_node and not self.connecting_from:
            n = self.nodes[self.selected_node]
            wx, wy = self.screen_to_world(event.x, event.y)
            
            raw_x = wx - self.drag_data["x"]
            raw_y = wy - self.drag_data["y"]
            
            if self.snap_to_grid.get():
                raw_x = round(raw_x / self.grid_size) * self.grid_size
                raw_y = round(raw_y / self.grid_size) * self.grid_size
                
            dx = (raw_x - n["x"]) * self.zoom_level
            dy = (raw_y - n["y"]) * self.zoom_level
            
            if dx != 0 or dy != 0:
                n["x"], n["y"] = raw_x, raw_y
                self.canvas.move(self.selected_node, dx, dy)
                self.draw_edges()

    def on_lmb_up(self, event):
        if getattr(self, 'active_slider', None):
            self.save_state()
            self.active_slider = None
            self.update_status("Значение слайдера сохранено")
            return
            
        if getattr(self, 'panning', False):
            self.panning = False
        elif self.resizing_node:
            self.resizing_node = None
            self.save_state()
            self.update_status("Пропорции узла обновлены")
        elif getattr(self, 'selected_node', None) and not self.connecting_from and not self.view_mode.get():
            self.save_state()

    def on_rmb_down(self, event):
        if self.view_mode.get(): 
            return
        
        self.last_rmb_x, self.last_rmb_y = self.screen_to_world(event.x, event.y)
        
        clicked_items = self.canvas.find_withtag("current")
        clicked_edge_idx = None
        if clicked_items:
            tags = self.canvas.gettags(clicked_items[0])
            if "edge" in tags:
                for tag in tags:
                    if tag.startswith("edge_idx_"):
                        clicked_edge_idx = int(tag.split("_")[-1])
                        
        node_id = self.get_node_at(event.x, event.y)
        
        if clicked_edge_idx is not None and node_id is None:
            if self.selected_node:
                self.set_node_selected(self.selected_node, False)
                self.selected_node = None
            self.selected_edge = clicked_edge_idx
            self.render()
            self.edge_menu.tk_popup(event.x_root, event.y_root)
            return
            
        if self.selected_node and self.selected_node != node_id:
             self.set_node_selected(self.selected_node, False)
             prev = self.selected_node
             self.selected_node = None
             if prev in self.nodes:
                 self.canvas.delete(prev)
                 self.draw_node(prev, self.nodes[prev])
             
        self.selected_node = node_id
        
        if self.selected_node:
            self.selected_edge = None
            self.render() 
            self.set_node_selected(self.selected_node, True)
            self.node_menu.tk_popup(event.x_root, event.y_root)
        else:
            self.selected_edge = None
            self.render()
            self.bg_menu.tk_popup(event.x_root, event.y_root)

    def reset_node_scale(self):
        if self.view_mode.get(): 
            return
        if self.selected_node:
            self.nodes[self.selected_node]["scale"] = 1.0
            self.canvas.delete(self.selected_node)
            self.draw_node(self.selected_node, self.nodes[self.selected_node])
            self.draw_edges()
            self.save_state()
            self.update_status("Размер узла восстановлен к базовому")

    def set_node_selected(self, node_id, is_selected):
        if node_id not in self.nodes: 
            return
        n = self.nodes[node_id]
        
        hide_border = n.get("hide_border", False)
        
        default_colors = self.colors.get(n["type"], self.colors["Текст"])
        b_color = n.get("border_color", default_colors["border"])
        b_opacity = n.get("border_opacity", 1.0)
        
        blended_border = self.blend_color(b_color, "#FFFFFF", b_opacity)
        
        if is_selected:
            border_col = blended_border if not hide_border else "#0078D4"
            border_width = 2
            border_dash = () if not hide_border else (4, 4)
        else:
            border_col = blended_border if not hide_border else ""
            border_width = 1
            border_dash = ()
        
        items = self.canvas.find_withtag(f"{node_id}_bg")
        if items:
            self.canvas.itemconfig(items[0], outline=border_col, width=border_width, dash=border_dash)

    def calculate_node_size(self, n_type, content):
        lines = content.split('\n')
        max_len = max(map(len, lines), default=0)
        max_len = max(max_len, 10)
        
        w = max(160, max_len * 8 + 40)
        h = max(60, len(lines) * 20 + 45)
        
        if n_type == "Прогресс бар": 
            h = 80
        elif n_type == "Регулятор":
            is_numeric, _, _ = self._parse_slider_config(lines)
            if is_numeric:
                h = 145; w = max(160, max_len * 8 + 40)
            else:
                h = 95; w = max(200, max_len * 8 + 40)
        elif n_type == "Сводка":
            table_obj = getattr(self, '_cached_vars', {}).get(lines[0].strip() if lines else "")
            if isinstance(table_obj, DataTable):
                w = max(250, len(table_obj.headers) * 80 + 40)
                h = max(100, len(table_obj.rows) * 24 + 65)
            else:
                w = max(250, max_len * 9 + 40)
                h = max(100, len(lines) * 24 + 40)
        elif n_type == "Страница": 
            w = max(260, max_len * 7 + 40)
            h = max(200, len(lines) * 22 + 60)
        elif n_type == "Функция":
            h = max(110, len(lines) * 20 + 80)
            w = max(220, max_len * 9 + 50)
        elif n_type == "Диаграмма":
            w = max(250, len(lines) * 45 + 60)
            h = max(200, 220)
        elif n_type == "Секторная диаграмма":
            w = max(300, 350)
            h = max(200, len(lines) * 20 + 80)
        elif n_type == "Переключатель":
            h = max(60, len(lines) * 20 + 45)
            w = max(180, max_len * 8 + 50)
        elif n_type == "Ссылка":
            w = max(200, max_len * 8 + 60)
            h = max(70, len(lines) * 20 + 45)
        elif n_type == "Часы":
            w, h = 200, 95
        elif n_type == "Магнитола":
            w, h = 280, 210
        elif n_type == "Контроллер":
            w, h = 260, 230
            
        return w, h

    def create_node(self, node_type, initial="", subtype="", at_x=None, at_y=None):
        if self.view_mode.get(): 
            return
        
        if at_x is None:
            at_x, at_y = self.screen_to_world(self.winfo_width()/2 - 50, self.winfo_height()/2 - 50)
            if hasattr(self, 'last_rmb_x'):
                at_x, at_y = self.last_rmb_x, self.last_rmb_y
            
        if node_type in ("Часы", "Магнитола", "Контроллер"):
            res = node_type
        else:
            dlg = NodeEditorDialog(self, node_type, initial_content=initial, subtype=subtype)
            if dlg.result is not None:
                res = dlg.result
            else:
                return

        w, h = self.calculate_node_size(node_type, res)
        
        if self.snap_to_grid.get():
            at_x = round(at_x / self.grid_size) * self.grid_size
            at_y = round(at_y / self.grid_size) * self.grid_size
            
        self.node_counter += 1
        node_id = f"node_{self.node_counter}"
        
        def_colors = self.colors.get(node_type, self.colors["Текст"])
        
        self.nodes[node_id] = {
            "id": node_id, "type": node_type, "subtype": subtype,
            "content": res,
            "x": at_x, "y": at_y, "w": w, "h": h, "scale": 1.0,
            "hide_border": False,
            "hide_content": False,
            "border_color": def_colors["border"],
            "bg_color": def_colors["bg"],
            "border_opacity": 1.0,
            "bg_opacity": 1.0,
            "content_opacity": 1.0,
            "lock_aspect_ratio": False,
            "aspect_ratio": w / h if h > 0 else 1.33
        }
        
        if node_type == "Часы":
            self.nodes[node_id]["clock_time"] = time.time()
            self.nodes[node_id]["is_running"] = True
            self.nodes[node_id]["last_update"] = time.time()
        elif node_type == "Магнитола":
            self.nodes[node_id]["playlist"] = []
            self.nodes[node_id]["track_idx"] = 0
            self.nodes[node_id]["is_playing"] = False
            self.nodes[node_id]["volume"] = 80
            self.nodes[node_id]["play_started_at"] = None
            self.nodes[node_id]["elapsed"] = 0.0
        elif node_type == "Контроллер":
            self.nodes[node_id]["scroll_idx"] = 0
            
        self.save_state()
        self.render()
        self.update_navigator_list()
        self.update_status(f"Добавлен узел {node_type}")

    def duplicate_node(self):
        if self.view_mode.get(): 
            return
        if getattr(self, 'selected_node', None) is None: 
            return
            
        orig = self.nodes[self.selected_node]
        self.node_counter += 1
        new_id = f"node_{self.node_counter}"
        
        new_node = copy.deepcopy(orig)
        new_node["id"] = new_id
        new_node["x"] += 30
        new_node["y"] += 30
        
        if new_node["type"] == "Часы":
            new_node["last_update"] = time.time()
            
        if self.snap_to_grid.get():
            new_node["x"] = round(new_node["x"] / self.grid_size) * self.grid_size
            new_node["y"] = round(new_node["y"] / self.grid_size) * self.grid_size
            
        self.nodes[new_id] = new_node
        self.set_node_selected(self.selected_node, False)
        self.selected_node = new_id
        self.save_state()
        
        self.render()
        self.update_navigator_list()
        self.update_status("Узел дублирован")

    def create_image_node(self):
        if self.view_mode.get(): 
            return
        filepath = filedialog.askopenfilename(filetypes=[("Изображения", "*.png *.jpg *.jpeg *.gif *.bmp *.webp")])
        if filepath:
            wx, wy = self.screen_to_world(self.winfo_width()/2, self.winfo_height()/2)
            if hasattr(self, 'last_rmb_x'):
                wx, wy = self.last_rmb_x, self.last_rmb_y
            self.create_image_node_from_file(filepath, wx, wy)

    def create_image_node_from_file(self, filepath, x, y, is_temp=False):
        caption = "Изображение" if is_temp else os.path.basename(filepath)
        if self.snap_to_grid.get():
            x = round(x / self.grid_size) * self.grid_size
            y = round(y / self.grid_size) * self.grid_size
            
        self.node_counter += 1
        node_id = f"node_{self.node_counter}"
        self.nodes[node_id] = {
            "id": node_id, "type": "Изображение", "content": caption,
            "filepath": filepath,
            "x": x, "y": y, "w": 200, "h": 200, "scale": 1.0,
            "hide_border": False,
            "hide_content": False,
            "border_color": "#9CA3AF",
            "bg_color": "#FFFFFF",
            "border_opacity": 1.0,
            "bg_opacity": 1.0,
            "content_opacity": 1.0,
            "lock_aspect_ratio": False,
            "aspect_ratio": 1.0
        }
        self.save_state()
        self.render()
        self.update_navigator_list()
        self.update_status("Изображение загружено")

    def edit_node_properties(self):
        if self.view_mode.get(): 
            return
        if not getattr(self, 'selected_node', None): 
            return
        n = self.nodes[self.selected_node]
        
        dlg = NodePropertiesDialog(self, self.selected_node, n)
        if dlg.result:
            self.save_state()
            self.render()
            self.update_status("Визуальные свойства обновлены")

    def edit_node(self):
        if self.view_mode.get(): 
            return
        if not getattr(self, 'selected_node', None): 
            return
        n = self.nodes[self.selected_node]
        if n["type"] == "Изображение":
            new_cap = simpledialog.askstring("Редактировать", "Подпись изображения:", initialvalue=n["content"])
            if new_cap is not None: 
                n["content"] = new_cap
        elif n["type"] == "Часы":
            self.edit_clock_node(n)
            return
        elif n["type"] == "Магнитола":
            self._magnitola_add_tracks(self.selected_node, n)
        elif n["type"] == "Контроллер":
            n_targets = len(self._get_controller_targets(self.selected_node))
            messagebox.showinfo("Контроллер", f"Подключено узлов: {n_targets}.\nПКМ на любом узле -> «Провести связь» -> кликните по контроллеру, чтобы добавить подключение.")
        else:
            dlg = NodeEditorDialog(self, n["type"], initial_content=n["content"], subtype=n.get("subtype", ""))
            if dlg.result is not None:
                n["content"] = dlg.result
        
        self.save_state()
        self.render()
        self.update_navigator_list()
        self.update_status("Содержимое обновлено")

    def edit_clock_node(self, n):
        clock_dlg = tk.Toplevel(self)
        clock_dlg.title("Настройки времени")
        clock_dlg.geometry("320x240")
        clock_dlg.configure(bg="#F3F3F3")
        clock_dlg.transient(self)
        clock_dlg.grab_set()
        
        dt = datetime.datetime.fromtimestamp(n.get("clock_time", time.time()))
        
        tk.Label(clock_dlg, text="Время (ЧЧ:ММ:СС):", font=("Segoe UI", 9), bg="#F3F3F3", fg="#1C1C1C").pack(pady=(12, 2))
        time_var = tk.StringVar(value=dt.strftime("%H:%M:%S"))
        time_ent = tk.Entry(clock_dlg, textvariable=time_var, font=("Consolas", 10), justify=tk.CENTER, bg="#FFFFFF", relief="flat", highlightthickness=1, highlightbackground="#E5E5E5")
        time_ent.pack(pady=2, ipady=3)
        
        tk.Label(clock_dlg, text="Дата (ДД.ММ.ГГГГ):", font=("Segoe UI", 9), bg="#F3F3F3", fg="#1C1C1C").pack(pady=(12, 2))
        date_var = tk.StringVar(value=dt.strftime("%d.%m.%Y"))
        date_ent = tk.Entry(clock_dlg, textvariable=date_var, font=("Consolas", 10), justify=tk.CENTER, bg="#FFFFFF", relief="flat", highlightthickness=1, highlightbackground="#E5E5E5")
        date_ent.pack(pady=2, ipady=3)
        
        is_running_var = tk.BooleanVar(value=n.get("is_running", True))
        ttk.Checkbutton(clock_dlg, text="Активный ход времени", variable=is_running_var).pack(pady=12)
        
        def apply_clock():
            try:
                new_dt = datetime.datetime.strptime(f"{date_var.get()} {time_var.get()}", "%d.%m.%Y %H:%M:%S")
                n["clock_time"] = new_dt.timestamp()
                n["is_running"] = is_running_var.get()
                n["last_update"] = time.time()
                self.save_state()
                self.render()
                clock_dlg.destroy()
            except ValueError:
                messagebox.showerror("Ошибка", "Неверный формат даты/времени")
                
        ttk.Button(clock_dlg, text="Сохранить", command=apply_clock).pack(pady=5)

    def delete_node(self):
        if self.view_mode.get(): 
            return
        
        if getattr(self, 'selected_node', None):
            node_to_delete = self.selected_node
            if self.nodes[node_to_delete]["type"] == "Магнитола" and self.nodes[node_to_delete].get("is_playing"):
                self._magnitola_stop_playback()
            self.edges = [e for e in self.edges if e[0] != node_to_delete and e[1] != node_to_delete]
            
            if node_to_delete in self.animated_items:
                del self.animated_items[node_to_delete]
            del self.nodes[node_to_delete]
            
            self.selected_node = None
            self.save_state()
            self.render()
            self.update_navigator_list()
            self.update_status("Узел удален")
            
        elif getattr(self, 'selected_edge', None) is not None:
            del self.edges[self.selected_edge]
            self.selected_edge = None
            self.save_state()
            self.render()
            self.update_status("Связь удалена")

    def start_connection(self):
        if self.view_mode.get(): 
            return
        self.connecting_from = getattr(self, 'selected_node', None)
        if self.connecting_from:
            self.update_status("Режим построения связи: выберите цель")

    def start_connection_from_selected(self):
        if self.view_mode.get(): 
            return
        if getattr(self, 'selected_node', None):
            self.start_connection()
        else:
            messagebox.showinfo("Инфо", "Выберите начальный узел")

    def render(self):
        self.canvas.delete("all")
        self.animated_items.clear()
        
        vars_dict = self.get_current_vars()
        self._cached_vars = vars_dict
        
        for node_id, n in self.nodes.items():
            if n["type"] in ["Часы", "Изображение"]: 
                continue
            
            display_content = n["content"]
            if n["type"] not in ["Переменная", "Регулятор", "Сводка"]:
                display_content = self.process_content(display_content, vars_dict)
                
            # Если размеры не кастомизированы пользователем вручную, рассчитываем их автоматически
            if "w" not in n or "h" not in n:
                w, h = self.calculate_node_size(n["type"], display_content)
                n["w"], n["h"] = w, h

        self.draw_grid()
        self.draw_edges()

        for node_id, n in self.nodes.items():
            self.draw_node(node_id, n)
            
        if getattr(self, 'selected_node', None):
            self.set_node_selected(self.selected_node, True)

    def draw_grid(self):
        self.canvas.delete("bg_grid")
        step = int(self.grid_size * self.zoom_level)
        if step < 6: 
            return
        
        w_width, w_height = self.canvas.winfo_width(), self.canvas.winfo_height()
        if w_width <= 1: 
            w_width = self.winfo_width()
        if w_height <= 1: 
            w_height = self.winfo_height()
            
        start_x = (self.offset_x % step) - step
        start_y = (self.offset_y % step) - step
        
        for x in range(int(start_x), w_width + step, step):
            self.canvas.create_line(x, 0, x, w_height, fill="#F3F3F3", tags="bg_grid")
        for y in range(int(start_y), w_height + step, step):
            self.canvas.create_line(0, y, w_width, y, fill="#F3F3F3", tags="bg_grid")

        self.canvas.create_line(0, self.offset_y, w_width, self.offset_y, fill="#E5E5E5", width=1, tags="bg_grid")
        self.canvas.create_line(self.offset_x, 0, self.offset_x, w_height, fill="#E5E5E5", width=1, tags="bg_grid")
        self.canvas.create_text(self.offset_x + 8, self.offset_y + 8, text="(0, 0)", anchor=tk.NW, fill="#7A7A7A", font=("Segoe UI", 8), tags="bg_grid")
        self.canvas.tag_lower("bg_grid")

    def draw_edges(self):
        self.canvas.delete("edge")
        for i, edge_data in enumerate(self.edges):
            u = edge_data[0]
            v = edge_data[1]
            direction = edge_data[2] if len(edge_data) > 2 else 1
            
            if u in self.nodes and v in self.nodes:
                n1, n2 = self.nodes[u], self.nodes[v]
                s1 = n1.get("scale", 1.0)
                s2 = n2.get("scale", 1.0)
                
                x1, y1 = self.world_to_screen(n1["x"] + (n1["w"]*s1)/2, n1["y"] + (n1["h"]*s1)/2)
                x2, y2 = self.world_to_screen(n2["x"] + (n2["w"]*s2)/2, n2["y"] + (n2["h"]*s2)/2)
                
                ctrl_x1 = x1 + (x2 - x1) / 2
                ctrl_y1 = y1
                ctrl_x2 = x1 + (x2 - x1) / 2
                ctrl_y2 = y2
                
                is_selected = getattr(self, 'selected_edge', None) == i
                
                color = "#0078D4" if is_selected else "#8A8A8A"
                shadow_color = "#E1F0FE" if is_selected else "#F3F3F3"
                width_base = 3 if is_selected else 2
                
                arrow_mode = tk.LAST
                if direction == 2: 
                    arrow_mode = tk.BOTH
                elif direction == 0: 
                    arrow_mode = tk.NONE
                
                tags = ("edge", f"edge_idx_{i}")
                
                self.canvas.create_line(x1, y1, ctrl_x1, ctrl_y1, ctrl_x2, ctrl_y2, x2, y2, smooth=True, fill=shadow_color, width=(width_base+2)*self.zoom_level, tags=tags)
                self.canvas.create_line(x1, y1, ctrl_x1, ctrl_y1, ctrl_x2, ctrl_y2, x2, y2, smooth=True, fill="", width=12*self.zoom_level, tags=tags)
                self.canvas.create_line(x1, y1, ctrl_x1, ctrl_y1, ctrl_x2, ctrl_y2, x2, y2, smooth=True, fill=color, width=width_base*self.zoom_level, arrow=arrow_mode, arrowshape=(12*self.zoom_level, 14*self.zoom_level, 4*self.zoom_level), tags=tags)

        self.canvas.tag_lower("edge")
        self.canvas.tag_lower("bg_grid")

    def _get_font(self, family, base_size, weight="normal", zs=1.0, overstrike=False, underline=False):
        size = max(4, int(base_size * zs))
        style = weight if weight != "normal" else ""
        if overstrike: 
            style = (style + " overstrike").strip()
        if underline: 
            style = (style + " underline").strip()
            
        if not style: 
            return (family, size)
        return (family, size, style)

    def _draw_code_with_highlighting(self, x, y, line, font, zs, node_tags, blended_bg, content_opacity, is_dark_bg):
        tokens = RE_CODE_TOKENS.findall(line)
        x_cursor = x
        for token in tokens:
            if is_dark_bg:
                # Пастельная тема синтаксиса для темного фона
                if token.startswith('"') or token.startswith("'"): 
                    base_col = "#E06C75" 
                elif token.startswith("#") or token.startswith("//") or token.startswith("/*"): 
                    base_col = "#5C6370" 
                elif token in KW_BLUE: 
                    base_col = "#61AFEF" 
                elif token.isdigit(): 
                    base_col = "#D19A66" 
                elif token.isspace() or (len(token) == 1 and token in '[]{}(),.:;=+-*!&|<>'): 
                    base_col = "#ABB2BF" 
                else: 
                    base_col = "#E5C07B"
            else:
                # Контрастная тема для светлого фона
                if token.startswith('"') or token.startswith("'"): 
                    base_col = "#A31515" 
                elif token.startswith("#") or token.startswith("//") or token.startswith("/*"): 
                    base_col = "#008000" 
                elif token in KW_BLUE: 
                    base_col = "#0000FF" 
                elif token.isdigit(): 
                    base_col = "#098658" 
                elif token.isspace() or (len(token) == 1 and token in '[]{}(),.:;=+-*!&|<>'): 
                    base_col = "#333333" 
                else: 
                    base_col = "#795E26"
                
            color = self.blend_color(base_col, blended_bg, content_opacity)
            txt_id = self.canvas.create_text(x_cursor, y, anchor=tk.NW, text=token, fill=color, font=font, tags=node_tags)
            bbox = self.canvas.bbox(txt_id)
            if bbox: 
                x_cursor = bbox[2] 

    def draw_node(self, node_id, n):
        """Интеллектуальная отрисовка узла с адаптивным ограничением контента от выходов за рамки."""
        zs = self.zoom_level * n.get("scale", 1.0)
        
        if n["type"] == "Изображение" and "orig_w" not in n:
            img_data = self.get_tk_image(n.get("filepath", ""), target_scale=zs)
            if img_data and isinstance(img_data, dict):
                n["orig_w"] = img_data["w"] / zs + 20
                n["orig_h"] = img_data["h"] / zs + 26 + 35
                n["w"], n["h"] = n["orig_w"], n["orig_h"]
        
        x, y = self.world_to_screen(n["x"], n["y"])
        w = n["w"] * zs
        h = n["h"] * zs
        header_h = 26 * zs
        
        display_content = n["content"]
        if n["type"] not in ["Переменная", "Регулятор", "Сводка"]:
            display_content = self.process_content(display_content, getattr(self, '_cached_vars', self.get_current_vars()))
            
        hide_border = n.get("hide_border", False)
        hide_content = n.get("hide_content", False)
        
        default_colors = self.colors.get(n["type"], self.colors["Текст"])
        border_color_raw = n.get("border_color", default_colors["border"])
        bg_color_raw = n.get("bg_color", default_colors["bg"])
        
        border_opacity = n.get("border_opacity", 1.0)
        bg_opacity = n.get("bg_opacity", 1.0)
        content_opacity = n.get("content_opacity", 1.0)
        
        blended_bg = self.blend_color(bg_color_raw, "#FFFFFF", bg_opacity)
        blended_border = self.blend_color(border_color_raw, "#FFFFFF", border_opacity)
        blended_header = self.blend_color(default_colors["header"], blended_bg, bg_opacity)
        blended_strip = self.blend_color(border_color_raw, blended_bg, border_opacity)
        
        # Интеллектуальный расчет контрастности текста
        adaptive_text_color = self.get_contrasting_text_color(bg_color_raw, bg_opacity)
        is_dark_bg = (adaptive_text_color == "#FFFFFF")
        
        blended_text_color = self.blend_color(adaptive_text_color, blended_bg, content_opacity)
        blended_secondary_color = self.blend_color("#5F5F5F" if not is_dark_bg else "#CCCCCC", blended_bg, content_opacity)
        
        rect_outline = blended_border if not hide_border else ""
        node_tags = ("node", node_id)
        
        self.canvas.create_rectangle(x, y, x+w, y+h, fill=blended_bg, outline=rect_outline, width=1, tags=node_tags + (f"{node_id}_bg",))
        
        if not hide_border:
            self.canvas.create_rectangle(x, y, x+(4*zs), y+h, fill=blended_strip, outline="", tags=node_tags)
        
        title = f"Функция {n.get('subtype', '')}".strip() if n["type"] == "Функция" else n["type"]
        
        if n["type"] == "Страница":
            self.canvas.create_rectangle(x+(4*zs), y, x+w, y+header_h, fill=blended_header, outline="", tags=node_tags)
            self.canvas.create_text(x+w/2, y+(13*zs), text="Браузер", font=self._get_font("Segoe UI", 8, "bold", zs), fill=blended_secondary_color, tags=node_tags)
        elif n["type"] == "Код":
            self.canvas.create_rectangle(x+(4*zs), y, x+w, y+header_h, fill=blended_header, outline="", tags=node_tags)
            lang = display_content.split("\n", 1)[0] if "\n" in display_content else "code"
            self.canvas.create_text(x+(14*zs), y+(5*zs), anchor=tk.NW, text=f"{lang}", fill=blended_secondary_color, font=self._get_font("Segoe UI", 9, "bold", zs), tags=node_tags)
        elif n["type"] != "Сводка":
            self.canvas.create_rectangle(x+(4*zs), y, x+w, y+header_h, fill=blended_header, outline="", tags=node_tags)
            self.canvas.create_text(x+(14*zs), y+(5*zs), anchor=tk.NW, text=title, fill=blended_text_color, font=self._get_font("Segoe UI", 9, "bold", zs), tags=node_tags)

        cx, cy = x + w/2, y + header_h + (h - header_h)/2
        pad_y = y + header_h + (10*zs)
        pad_x = x + (15*zs)
        
        # Ограничения автошрифтов
        lines_count = len(display_content.split('\n')) if display_content else 1
        available_height = max(30, h - header_h - (15*zs))
        auto_font_size = max(7, min(10, int(available_height / (lines_count * 1.6 * zs)) if lines_count > 1 else 10))

        if hide_content:
            self.canvas.create_text(cx, cy, text="[Скрыто]", font=self._get_font("Segoe UI", 9, "italic", zs), fill=blended_secondary_color, tags=node_tags)
        else:
            if n["type"] == "Сводка":
                lines = display_content.split("\n")
                t_name = lines[0].strip() if lines else "Таблица"
                self.canvas.create_text(x + (15*zs), y + (10*zs), anchor=tk.NW, text=f"Данные: {t_name}", font=self._get_font("Segoe UI", 11, "bold", zs), fill=self.blend_color("#B45309" if not is_dark_bg else "#FDBA74", blended_bg, content_opacity), tags=node_tags)
                
                table_obj = getattr(self, '_cached_vars', {}).get(t_name)
                row_h = 24 * zs
                font_bold = self._get_font("Segoe UI", 9, "bold", zs)
                font_norm = self._get_font("Segoe UI", 9, "normal", zs)
                start_y = y + (36*zs)
                table_w = w - (30*zs)
                
                if isinstance(table_obj, DataTable):
                    headers = table_obj.headers
                    num_cols = max(1, len(headers))
                    col_w = table_w / num_cols
                    
                    for j, h_col in enumerate(headers):
                        tx = x + (15*zs) + j*col_w
                        self.canvas.create_rectangle(tx, start_y, tx+col_w, start_y+row_h, fill=self.blend_color("#FFFBEB" if not is_dark_bg else "#451A03", blended_bg, content_opacity), outline=self.blend_color("#FDE68A", blended_bg, content_opacity), tags=node_tags)
                        self.canvas.create_text(tx+(8*zs), start_y+(4*zs), anchor=tk.NW, text=h_col, font=font_bold, fill=self.blend_color("#92400E" if not is_dark_bg else "#FDBA74", blended_bg, content_opacity), tags=node_tags)
                    
                    for i, row in enumerate(table_obj.rows):
                        ty = start_y + (i+1)*row_h
                        if ty + row_h > y + h - (10 * zs):
                            remaining = len(table_obj.rows) - i
                            self.canvas.create_text(x + (15*zs), ty + (4*zs), anchor=tk.NW, text=f"... еще {remaining} зап.", font=self._get_font("Segoe UI", 8, "italic", zs), fill=self.blend_color("#9CA3AF", blended_bg, content_opacity), tags=node_tags)
                            break
                            
                        row_bg = "#FFFDF5" if i % 2 != 0 else "#FFFFFF"
                        if is_dark_bg:
                            row_bg = "#2D1A0A" if i % 2 != 0 else "#1F1105"
                        for j, h_col in enumerate(headers):
                            tx = x + (15*zs) + j*col_w
                            self.canvas.create_rectangle(tx, ty, tx+col_w, ty+row_h, fill=self.blend_color(row_bg, blended_bg, content_opacity), outline=self.blend_color("#FDE68A", blended_bg, content_opacity), tags=node_tags)
                            
                            val = str(row._data.get(h_col, ""))
                            max_chars = max(2, int(col_w / (9 * 0.5 * zs)))
                            if len(val) > max_chars: 
                                val = val[:max_chars-2] + ".."
                            self.canvas.create_text(tx+(8*zs), ty+(4*zs), anchor=tk.NW, text=val, font=font_norm, fill=self.blend_color("#92400E" if not is_dark_bg else "#FFEDD5", blended_bg, content_opacity), tags=node_tags)

            elif n["type"] == "Часы":
                dt = datetime.datetime.fromtimestamp(n.get("clock_time", time.time()))
                time_str = dt.strftime("%H:%M:%S")
                date_str = dt.strftime("%d.%m.%Y")
                self.canvas.create_text(cx, cy - (8*zs), text=time_str, fill=self.blend_color("#EF4444", blended_bg, content_opacity), font=self._get_font("Consolas", 22, "bold", zs), tags=node_tags + (f"{node_id}_time",))
                self.canvas.create_text(cx, cy + (15*zs), text=date_str, fill=blended_secondary_color, font=self._get_font("Consolas", 12, "normal", zs), tags=node_tags + (f"{node_id}_date",))
                if not n.get("is_running", True):
                    self.canvas.create_text(x + w - (15*zs), y + header_h + (12*zs), text="⏸", fill=self.blend_color("#EF4444", blended_bg, content_opacity), font=self._get_font("Segoe UI", 10, zs=zs), tags=node_tags)

            elif n["type"] == "Магнитола":
                playlist = n.get("playlist", [])
                track_idx = n.get("track_idx", 0)
                track_name = "Плейлист пуст"
                if playlist and 0 <= track_idx < len(playlist):
                    track_name = os.path.basename(playlist[track_idx])
                    if len(track_name) > 26:
                        track_name = track_name[:24] + ".."
                elapsed = n.get("elapsed", 0.0)
                pos_str = f"{int(elapsed)//60:02d}:{int(elapsed)%60:02d}"
                self.canvas.create_text(cx, y + header_h + (18*zs), text=track_name, fill=self.blend_color("#F9FAFB", blended_bg, content_opacity), font=self._get_font("Segoe UI", 10, "bold", zs), tags=node_tags)
                self.canvas.create_text(cx, y + header_h + (38*zs), text=f"Трек {track_idx+1 if playlist else 0}/{len(playlist)}   {pos_str}", fill=self.blend_color("#9CA3AF", blended_bg, content_opacity), font=self._get_font("Segoe UI", 9, zs=zs), tags=node_tags + (f"{node_id}_pos",))
                self.canvas.create_text(x + w - (16*zs), y + header_h + (12*zs), text="+", fill=self.blend_color("#0EA5E9", blended_bg, content_opacity), font=self._get_font("Segoe UI", 13, "bold", zs), tags=node_tags)
                btn_y = y + h - (30*zs)
                play_glyph = "⏸" if n.get("is_playing", False) else "▶"
                self.canvas.create_text(x + w*0.28, btn_y, text="⏮", fill=blended_text_color, font=self._get_font("Segoe UI", 15, zs=zs), tags=node_tags)
                self.canvas.create_text(x + w*0.50, btn_y, text=play_glyph, fill=self.blend_color("#0EA5E9", blended_bg, content_opacity), font=self._get_font("Segoe UI", 17, "bold", zs), tags=node_tags)
                self.canvas.create_text(x + w*0.72, btn_y, text="⏭", fill=blended_text_color, font=self._get_font("Segoe UI", 15, zs=zs), tags=node_tags)

            elif n["type"] == "Контроллер":
                targets = self._get_controller_targets(node_id)
                row_h_local = 28
                if not targets:
                    self.canvas.create_text(pad_x, pad_y, anchor=tk.NW, text="Нет связанных узлов.\nПКМ на узле -> «Провести связь»,\nзатем кликните по этому узлу.", fill=blended_secondary_color, font=self._get_font("Segoe UI", 9, zs=zs), justify=tk.LEFT, tags=node_tags)
                else:
                    max_rows = max(1, int((n["h"] - 40) / row_h_local))
                    for i, (t_id, t_node) in enumerate(targets):
                        if i >= max_rows:
                            self.canvas.create_text(pad_x, pad_y + i*(row_h_local*zs), anchor=tk.NW, text=f"... еще {len(targets)-max_rows}", font=self._get_font("Segoe UI", 8, "italic", zs), fill=blended_secondary_color, tags=node_tags)
                            break
                        row_y = y + header_h + (10*zs) + i*(row_h_local*zs)
                        label = f"{t_node['type']} · {t_id.replace('node_', '#')}"
                        self.canvas.create_text(x + (14*zs), row_y + (13*zs), anchor=tk.W, text=label, fill=blended_text_color, font=self._get_font("Segoe UI", 9, zs=zs), tags=node_tags)
                        state_glyph, glyph_color = self._controller_state_glyph(t_node)
                        self.canvas.create_text(x + w - (20*zs), row_y + (13*zs), anchor=tk.E, text=state_glyph, fill=self.blend_color(glyph_color, blended_bg, content_opacity), font=self._get_font("Segoe UI", 12, "bold", zs), tags=node_tags)
                        if i < len(targets) - 1 and i < max_rows - 1:
                            self.canvas.create_line(x+(10*zs), row_y+(24*zs), x+w-(10*zs), row_y+(24*zs), fill=self.blend_color("#E5E5E5", blended_bg, content_opacity), tags=node_tags)

            elif n["type"] == "Ссылка":
                link_font = self._get_font("Segoe UI", auto_font_size, zs=zs, underline=True)
                self.canvas.create_text(pad_x, pad_y + (5*zs), anchor=tk.NW, text=display_content, fill=self.blend_color("#0078D4" if not is_dark_bg else "#60A5FA", blended_bg, content_opacity), font=link_font, width=w-(55*zs), tags=node_tags)
                
                btn_sz = 20 * zs
                btn_x = x + w - btn_sz - (10*zs)
                btn_y = pad_y + (2*zs)
                self.canvas.create_rectangle(btn_x, btn_y, btn_x + btn_sz, btn_y + btn_sz, fill=self.blend_color("#F0F9FF" if not is_dark_bg else "#1E3A8A", blended_bg, content_opacity), outline=self.blend_color("#0078D4", blended_bg, content_opacity), tags=node_tags)
                self.canvas.create_text(btn_x + btn_sz/2, btn_y + btn_sz/2, text="▶", fill=self.blend_color("#0078D4" if not is_dark_bg else "#60A5FA", blended_bg, content_opacity), font=self._get_font("Segoe UI", 10, zs=zs), tags=node_tags)

            elif n["type"] == "Код":
                lines = display_content.split("\n")
                lang = lines[0] if lines else "code"
                code_text = "\n".join(lines[1:]) if len(lines) > 1 else ""
                
                max_w = w - (30 * zs)
                max_h = h - header_h - (15 * zs)
                wrapped_lines, f_size = self.fit_text_to_box(code_text, "Consolas", max_w, max_h, zs, is_code=True)
                
                curr_y = pad_y
                font_code = self._get_font("Consolas", f_size, zs=zs)
                line_h = (f_size + 6) * zs
                for line in wrapped_lines:
                    self._draw_code_with_highlighting(pad_x, curr_y, line, font_code, zs, node_tags, blended_bg, content_opacity, is_dark_bg)
                    curr_y += line_h
                
            elif n["type"] == "Таблица":
                lines = display_content.split("\n")
                row_h = 24 * zs
                font_bold = self._get_font("Segoe UI", auto_font_size, "bold", zs)
                font_norm = self._get_font("Segoe UI", auto_font_size, "normal", zs)
                
                for i, line in enumerate(lines):
                    ty = pad_y + i*row_h
                    if ty + row_h > y + h - (10 * zs):
                        remaining = len(lines) - i
                        self.canvas.create_text(pad_x, ty + (2*zs), anchor=tk.NW, text=f"... еще {remaining} стр.", font=self._get_font("Segoe UI", auto_font_size, "italic", zs), fill=self.blend_color("#9CA3AF", blended_bg, content_opacity), tags=node_tags)
                        break
                        
                    cols = line.split(",")
                    col_w = (w-(30*zs)) / max(1, len(cols))
                    c_font = font_bold if i == 0 else font_norm
                    
                    for j, col in enumerate(cols):
                        tx = pad_x + j*col_w
                        row_bg = "#FAF9F8" if i % 2 == 0 else "#FFFFFF"
                        if is_dark_bg:
                            row_bg = "#2D2D2D" if i % 2 == 0 else "#1C1C1C"
                        self.canvas.create_rectangle(tx, ty, tx+col_w, ty+row_h, fill=self.blend_color(row_bg, blended_bg, content_opacity), outline=self.blend_color("#E5E5E5" if not is_dark_bg else "#3F3F3F", blended_bg, content_opacity), tags=node_tags)
                        
                        col_text = col.strip()
                        max_chars = max(2, int(col_w / (auto_font_size * 0.5 * zs)))
                        if len(col_text) > max_chars:
                            col_text = col_text[:max_chars-2] + ".."
                        self.canvas.create_text(tx+(8*zs), ty+(4*zs), anchor=tk.NW, text=col_text, font=c_font, fill=blended_text_color, tags=node_tags)

            elif n["type"] == "Регулятор":
                lines = display_content.split("\n")
                var_name, var_val = "Var", "0"
                if lines and "=" in lines[0]:
                    parts = lines[0].split("=", 1)
                    var_name, var_val = parts[0].strip(), parts[1].strip()

                is_numeric, range_vals, list_vals = self._parse_slider_config(lines)

                self.canvas.create_text(pad_x, pad_y, anchor=tk.NW, text=f"{var_name} = {var_val}", font=self._get_font("Segoe UI", 10, "bold", zs), fill=blended_text_color, tags=node_tags)

                if is_numeric:
                    min_v, max_v = range_vals[0], range_vals[1]
                    if max_v < min_v: 
                        max_v = min_v
                    try: 
                        val = float(var_val)
                    except: 
                        val = min_v

                    ratio = (val - min_v) / (max_v - min_v) if max_v != min_v else 0
                    ratio = max(0, min(1, ratio))

                    knob_cx = x + w/2
                    available_knob_h = h - header_h - (25 * zs)
                    knob_cy = pad_y + available_knob_h / 2
                    knob_r = min(35 * zs, available_knob_h * 0.4, w * 0.35)
                    knob_r = max(5 * zs, knob_r)

                    self.canvas.create_arc(
                        knob_cx - knob_r, knob_cy - knob_r,
                        knob_cx + knob_r, knob_cy + knob_r,
                        start=225, extent=-270, style=tk.ARC,
                        outline=self.blend_color("#E5E5E5" if not is_dark_bg else "#3F3F3F", blended_bg, content_opacity), width=max(1.0, 4*zs), tags=node_tags
                    )

                    if ratio > 0:
                        self.canvas.create_arc(
                            knob_cx - knob_r, knob_cy - knob_r,
                            knob_cx + knob_r, knob_cy + knob_r,
                            start=225, extent=-(270 * ratio), style=tk.ARC,
                            outline=self.blend_color(border_color_raw, blended_bg, content_opacity), width=max(1.0, 4*zs), tags=node_tags
                        )

                    inner_r = knob_r * 0.7
                    self.canvas.create_oval(
                        knob_cx - inner_r, knob_cy - inner_r + max(1.0, 2*zs),
                        knob_cx + inner_r, knob_cy + inner_r + max(1.0, 2*zs),
                        fill=self.blend_color("#E5E5E5" if not is_dark_bg else "#1C1C1C", blended_bg, content_opacity), outline="", tags=node_tags
                    )
                    self.canvas.create_oval(
                        knob_cx - inner_r, knob_cy - inner_r,
                        knob_cx + inner_r, knob_cy + inner_r,
                        fill=self.blend_color("#FFFFFF" if not is_dark_bg else "#2D2D2D", blended_bg, content_opacity), outline=self.blend_color("#CCCCCC" if not is_dark_bg else "#4F4F4F", blended_bg, content_opacity), width=max(1.0, 1.5*zs), tags=node_tags
                    )

                    deg = 225 - (270 * ratio)
                    rad = math.radians(deg)
                    ix1 = knob_cx + (inner_r * 0.5) * math.cos(rad)
                    iy1 = knob_cy - (inner_r * 0.5) * math.sin(rad)
                    ix2 = knob_cx + (inner_r * 0.9) * math.cos(rad)
                    iy2 = knob_cy - (inner_r * 0.9) * math.sin(rad)

                    self.canvas.create_line(ix1, iy1, ix2, iy2, fill=self.blend_color(border_color_raw, blended_bg, content_opacity), width=max(1.0, 3*zs), capstyle=tk.ROUND, tags=node_tags)
                    
                    display_val = var_val
                    if len(display_val) > 7: 
                        display_val = display_val[:5] + ".."
                    
                    lbl_size = max(5, min(10, int(knob_r * 0.3 / zs)))
                    self.canvas.create_text(knob_cx, knob_cy, text=display_val, fill=blended_secondary_color, font=self._get_font("Segoe UI", lbl_size, "bold", zs), tags=node_tags)

                else:
                    bar_y = pad_y + (25*zs)
                    btn_w = 25 * zs
                    
                    self.canvas.create_rectangle(pad_x, bar_y, pad_x + btn_w, bar_y + (22*zs), fill=self.blend_color("#F3F3F3" if not is_dark_bg else "#3F3F3F", blended_bg, content_opacity), outline=self.blend_color("#CCCCCC" if not is_dark_bg else "#4F4F4F", blended_bg, content_opacity), tags=node_tags)
                    self.canvas.create_text(pad_x + btn_w/2, bar_y + (11*zs), text="◀", fill=blended_secondary_color, font=self._get_font("Segoe UI", 9, zs=zs), tags=node_tags)

                    self.canvas.create_rectangle(pad_x + w - 30*zs - btn_w, bar_y, pad_x + w - 30*zs, bar_y + (22*zs), fill=self.blend_color("#F3F3F3" if not is_dark_bg else "#3F3F3F", blended_bg, content_opacity), outline=self.blend_color("#CCCCCC" if not is_dark_bg else "#4F4F4F", blended_bg, content_opacity), tags=node_tags)
                    self.canvas.create_text(pad_x + w - 30*zs - btn_w/2, bar_y + (11*zs), text="▶", fill=blended_secondary_color, font=self._get_font("Segoe UI", 9, zs=zs), tags=node_tags)

                    display_val = var_val
                    if len(display_val) > 15: 
                        display_val = display_val[:12] + "..."
                    self.canvas.create_text(pad_x + (w - 30*zs)/2, bar_y + (11*zs), text=display_val, fill=blended_text_color, font=self._get_font("Segoe UI", 9, "bold", zs), tags=node_tags)

            elif n["type"] == "Прогресс бар":
                parts = display_content.split("|")
                lbl = parts[0].strip() if len(parts) > 0 else "Progress"
                
                current_val = 50.0
                max_val = 100.0
                display_text = "50%"
                
                if len(parts) > 1:
                    val_str = parts[1].strip()
                    if '/' in val_str:
                        v_parts = val_str.split('/')
                        try:
                            current_val = float(v_parts[0].strip())
                            max_val = float(v_parts[1].strip())
                            if max_val == 0: 
                                max_val = 1.0 
                            
                            c_fmt = int(current_val) if current_val.is_integer() else current_val
                            m_fmt = int(max_val) if max_val.is_integer() else max_val
                            display_text = f"{c_fmt} / {m_fmt}"
                        except: 
                            pass
                    else:
                        val_str = val_str.replace('%', '').strip()
                        try:
                            current_val = float(val_str)
                            c_fmt = int(current_val) if current_val.is_integer() else current_val
                            display_text = f"{c_fmt}%"
                        except: 
                            pass
                
                render_ratio = min(1.0, max(0.0, current_val / max_val))
                
                self.canvas.create_text(pad_x, pad_y, anchor=tk.NW, text=lbl, font=self._get_font("Segoe UI", 10, "bold", zs), fill=blended_text_color, tags=node_tags)
                bar_y = pad_y + (25*zs)
                
                if bar_y + (16*zs) <= y + h - (5*zs):
                    self.canvas.create_rectangle(pad_x, bar_y, x+w-(15*zs), bar_y+(16*zs), fill=self.blend_color("#F3F3F3" if not is_dark_bg else "#2D2D2D", blended_bg, content_opacity), outline=self.blend_color("#E5E5E5" if not is_dark_bg else "#4F4F4F", blended_bg, content_opacity), tags=node_tags)
                    
                    fill_w = (w - (30*zs)) * render_ratio
                    if fill_w > 0:
                        self.canvas.create_rectangle(pad_x, bar_y, pad_x+fill_w, bar_y+(16*zs), fill=self.blend_color(border_color_raw, blended_bg, content_opacity), outline="", tags=node_tags)
                        
                    text_color = "#5F5F5F" if render_ratio < 0.55 else "#FFFFFF"
                    if is_dark_bg and render_ratio < 0.55:
                        text_color = "#E5E5E5"
                    self.canvas.create_text(cx, bar_y+(8*zs), text=display_text, fill=self.blend_color(text_color, blended_bg, content_opacity), font=self._get_font("Segoe UI", 8, "bold", zs), tags=node_tags)
                
            elif n["type"] == "Функция":
                func_text = display_content
                res_str = None
                is_error = False

                result, is_comp, err_msg = evaluate_math_expression(func_text)

                if err_msg:
                    is_error = True
                    res_str = err_msg if "Символьно" not in err_msg else "Символьно / Ошибка"
                else:
                    if isinstance(result, bool):
                        res_str = "ИСТИНА" if result else "ЛОЖЬ"
                    else:
                        res_str = str(result)

                res_bg_y = y + h - (38*zs)
                formula_cy = pad_y + (res_bg_y - pad_y) / 2 - (4*zs)

                # Многострочная вписка формулы во избежание выхода за пределы по ширине
                max_w = w - (30 * zs)
                max_h = res_bg_y - pad_y - (5 * zs)
                wrapped_math, math_f_size = self.fit_text_to_box(func_text, "Segoe UI", max_w, max_h, zs)
                
                curr_math_y = pad_y
                math_line_h = math_f_size * 1.35 * zs
                for line in wrapped_math:
                    self.canvas.create_text(cx, curr_math_y, anchor=tk.N, text=line, fill=blended_text_color, font=self._get_font("Segoe UI", math_f_size, "italic", zs), justify=tk.CENTER, tags=node_tags)
                    curr_math_y += math_line_h

                self.canvas.create_line(x + (15*zs), res_bg_y - (6*zs), x + w - (15*zs), res_bg_y - (6*zs), fill=self.blend_color("#E5E5E5" if not is_dark_bg else "#4F4F4F", blended_bg, content_opacity), dash=(4, 2), tags=node_tags)

                res_color = "#0078D4"
                bg_color = "#F0F9FF"
                
                if not is_error and isinstance(result, bool):
                    if result:
                        res_color = "#10B981"
                        bg_color = "#ECFDF5" if not is_dark_bg else "#064E3B"
                    else:
                        res_color = "#EF4444"
                        bg_color = "#FEF2F2" if not is_dark_bg else "#7F1D1D"
                elif is_error:
                    res_color = "#F59E0B"
                    bg_color = "#FFFBEB" if not is_dark_bg else "#78350F"
                    res_str = res_str or "Символьно"

                res_text = f"= {res_str}" if res_str else "= ..."
                
                # Усекаем текст результата, если узел слишком узок
                max_chars = max(3, int((w - 30*zs) / (11 * 0.55 * zs)))
                if len(res_text) > max_chars:
                    res_text = res_text[:max_chars-2] + ".."
                    
                self.canvas.create_rectangle(x + (12*zs), res_bg_y, x + w - (12*zs), y + h - (10*zs), fill=self.blend_color(bg_color, blended_bg, content_opacity), outline=self.blend_color(res_color, blended_bg, content_opacity), width=max(1.0, 1*zs), tags=node_tags)
                self.canvas.create_text(cx, res_bg_y + (13*zs), text=res_text, fill=self.blend_color(res_color, blended_bg, content_opacity), font=self._get_font("Segoe UI", 11, "bold", zs), justify=tk.CENTER, tags=node_tags)
                
            elif n["type"] == "Список":
                items = [it.strip() for it in display_content.split("\n") if it.strip()]
                checked = n.get("checked_items", [])
                
                max_w = w - (40 * zs)
                max_h = h - header_h - (15 * zs)
                
                # Ищем оптимальный размер шрифта для списка
                f_size = 10
                for test_size in range(10, 5, -1):
                    char_width = test_size * 0.45 * zs
                    chars_per_line = max(5, int(max_w / char_width))
                    import textwrap
                    total_lines = 0
                    for item in items:
                        total_lines += len(textwrap.wrap(item, width=chars_per_line))
                    line_height = test_size * 1.5 * zs
                    if total_lines * line_height <= max_h:
                        f_size = test_size
                        break
                    f_size = test_size
                    
                char_width = f_size * 0.45 * zs
                chars_per_line = max(5, int(max_w / char_width))
                line_height = f_size * 1.5 * zs
                
                font_norm = self._get_font("Segoe UI", f_size, "normal", zs)
                font_strike = self._get_font("Segoe UI", f_size, "normal", zs, overstrike=True)
                
                current_y = pad_y
                item_idx = 0
                import textwrap
                
                for item in items:
                    is_checked = item_idx in checked
                    bullet_col = "#9CA3AF" if is_checked else border_color_raw
                    text_col = "#9CA3AF" if is_checked else adaptive_text_color
                    f_style = font_strike if is_checked else font_norm
                    
                    wrapped_item_lines = textwrap.wrap(item, width=chars_per_line)
                    
                    if current_y + line_height > y + h - (10 * zs):
                        remaining = len(items) - item_idx
                        self.canvas.create_text(pad_x + (10 * zs), current_y, anchor=tk.NW, text=f"... еще {remaining}", fill=self.blend_color("#9CA3AF", blended_bg, content_opacity), font=self._get_font("Segoe UI", f_size, "italic", zs), tags=node_tags)
                        break
                        
                    r = 2 * zs
                    self.canvas.create_oval(pad_x, current_y + (f_size * 0.7 * zs) - r, pad_x + (2 * r), current_y + (f_size * 0.7 * zs) + r, fill=self.blend_color(bullet_col, blended_bg, content_opacity), outline="", tags=node_tags)
                    
                    for idx_line, line in enumerate(wrapped_item_lines):
                        if current_y + line_height > y + h - (10 * zs):
                            self.canvas.create_text(pad_x + (10 * zs), current_y, anchor=tk.NW, text="...", fill=self.blend_color(text_col, blended_bg, content_opacity), font=f_style, tags=node_tags)
                            current_y += line_height
                            break
                        self.canvas.create_text(pad_x + (10 * zs), current_y, anchor=tk.NW, text=line, fill=self.blend_color(text_col, blended_bg, content_opacity), font=f_style, tags=node_tags)
                        current_y += line_height
                        
                    item_idx += 1
                
            elif n["type"] == "Переключатель":
                state = n.get("state", 0)
                box_sz = 16 * zs
                box_x = pad_x
                box_y = pad_y
                
                self.canvas.create_rectangle(box_x, box_y, box_x + box_sz, box_y + box_sz, fill=self.blend_color("#FFFFFF" if not is_dark_bg else "#2D2D2D", blended_bg, content_opacity), outline=self.blend_color("#CCCCCC" if not is_dark_bg else "#5F5F5F", blended_bg, content_opacity), width=1.5*zs, tags=node_tags)
                
                if state == 1: 
                    self.canvas.create_line(box_x + 3*zs, box_y + 8*zs, box_x + 7*zs, box_y + 12*zs, box_x + 13*zs, box_y + 3*zs, fill=self.blend_color("#10B981", blended_bg, content_opacity), width=2.5*zs, capstyle=tk.ROUND, joinstyle=tk.ROUND, tags=node_tags)
                elif state == 2: 
                    self.canvas.create_line(box_x + 4*zs, box_y + 4*zs, box_x + 12*zs, box_y + 12*zs, fill=self.blend_color("#EF4444", blended_bg, content_opacity), width=2.5*zs, capstyle=tk.ROUND, tags=node_tags)
                    self.canvas.create_line(box_x + 12*zs, box_y + 4*zs, box_x + 4*zs, box_y + 12*zs, fill=self.blend_color("#EF4444", blended_bg, content_opacity), width=2.5*zs, capstyle=tk.ROUND, tags=node_tags)
                    
                max_w = w - box_sz - (25 * zs)
                max_h = h - header_h - (10 * zs)
                wrapped_lines, f_size = self.fit_text_to_box(display_content, "Segoe UI", max_w, max_h, zs)
                
                f_style_norm = self._get_font("Segoe UI", f_size, "normal", zs, overstrike=(state==2))
                t_color = "#9CA3AF" if state == 2 else adaptive_text_color
                
                curr_y = pad_y - (2 * zs)
                line_h = f_size * 1.35 * zs
                for line in wrapped_lines:
                    if curr_y + line_h > y + h - (5 * zs):
                        break
                    self.canvas.create_text(box_x + box_sz + (10*zs), curr_y, anchor=tk.NW, text=line, fill=self.blend_color(t_color, blended_bg, content_opacity), font=f_style_norm, tags=node_tags)
                    curr_y += line_h

            elif n["type"] == "Страница":
                content = display_content
                global_styles = {}
                
                style_match = RE_HTML_STYLE_BLOCK.search(content)
                if style_match:
                    style_text = style_match.group(1)
                    for rule_match in RE_CSS_RULES.finditer(style_text):
                        selectors = [s.strip() for s in rule_match.group(1).split(',')]
                        css_dict = {}
                        for prop in rule_match.group(2).split(';'):
                            if ':' in prop:
                                k, v = prop.split(':', 1)
                                css_dict[k.strip().lower()] = v.strip()
                        for sel in selectors: 
                            global_styles[sel] = css_dict
                    content = RE_HTML_STYLE_BLOCK.sub('', content)
                    
                content = content.replace('<br>', '\n').replace('<br/>', '\n').replace('<br />', '\n').replace('</p>', '\n')
                lines = [line for line in content.split('\n') if line.strip() or line == '']
                
                current_y = pad_y
                for line in lines:
                    if not line.strip() and "<" not in line: 
                        current_y += 10 * zs
                        continue
                        
                    # Безопасное отсечение по высоте во избежание вертикального переполнения HTML
                    if current_y + (auto_font_size * 2 * zs) > y + h - (10 * zs):
                        self.canvas.create_text(pad_x, current_y, anchor=tk.NW, text="...", font=self._get_font("Segoe UI", auto_font_size, "italic", zs), fill=blended_secondary_color, tags=node_tags)
                        break
                        
                    f_family, f_size, f_weight = "Segoe UI", auto_font_size, "normal"
                    text_color = adaptive_text_color
                    bg_color = None
                    is_underline = False
                    
                    tag_match = RE_HTML_TAG.search(line)
                    if tag_match:
                        tag_name = tag_match.group(1).lower()
                        attrs_str = tag_match.group(2)
                        
                        if tag_name in global_styles:
                            css = global_styles[tag_name]
                            text_color = css.get('color', text_color)
                            bg_color = css.get('background-color', css.get('background', bg_color))
                            if 'font-size' in css:
                                fs = re.sub(r'\D', '', css['font-size'])
                                if fs: f_size = int(fs)
                            if 'font-weight' in css: f_weight = css['font-weight']
                        
                        class_match = RE_HTML_CLASS.search(attrs_str)
                        if class_match:
                            for c in class_match.group(1).split():
                                c_sel = f".{c}"
                                if c_sel in global_styles:
                                    css = global_styles[c_sel]
                                    text_color = css.get('color', text_color)
                                    bg_color = css.get('background-color', css.get('background', bg_color))
                                    if 'font-size' in css:
                                        fs = re.sub(r'\D', '', css['font-size'])
                                        if fs: f_size = int(fs)
                                    if 'font-weight' in css: f_weight = css['font-weight']
                        
                        style_attr_match = RE_HTML_STYLE_ATTR.search(attrs_str)
                        if style_attr_match:
                            for prop in style_attr_match.group(1).split(';'):
                                if ':' in prop:
                                    k, v = prop.split(':', 1)
                                    k = k.strip().lower()
                                    v = v.strip()
                                    if k == 'color': text_color = v
                                    elif k in ('background', 'background-color'): bg_color = v
                                    elif k == 'font-size':
                                        fs = re.sub(r'\D', '', v)
                                        if fs: f_size = int(fs)
                                    elif k == 'font-weight': f_weight = v

                    lower_line = line.lower()
                    is_list_item = False
                    if "<h1>" in lower_line or "<h1 " in lower_line: f_size, f_weight = max(f_size, 14), "bold"
                    elif "<h2>" in lower_line or "<h2 " in lower_line: f_size, f_weight = max(f_size, 12), "bold"
                    elif "<h3>" in lower_line or "<h3 " in lower_line: f_size, f_weight = max(f_size, 11), "bold"
                    elif "<h4>" in lower_line or "<h4 " in lower_line: f_size, f_weight = max(f_size, 10), "bold"
                    elif "<b>" in lower_line or "<strong>" in lower_line: f_weight = "bold"
                    elif "<i>" in lower_line or "<em>" in lower_line: f_weight = "italic"
                    elif "<u>" in lower_line: is_underline = True
                    elif "<mark>" in lower_line or "<mark " in lower_line: bg_color = bg_color or "#FFF9C4" 
                    elif "<li>" in lower_line or "<li " in lower_line: is_list_item = True
                    elif "<a " in lower_line:
                        is_underline = True
                        if text_color == adaptive_text_color: text_color = "#0078D4"
                        
                    if "<header>" in lower_line or "<header " in lower_line or "<footer>" in lower_line or "<footer " in lower_line:
                        bg_color = bg_color or "#F3F3F3"
                        if "<footer" in lower_line: f_size = min(f_size, 9)
                    if "<code>" in lower_line or "<code " in lower_line:
                        f_family = "Consolas"
                        bg_color = bg_color or "#F1F5F9"
                        if text_color == adaptive_text_color: text_color = "#D97706"

                    clean_text = RE_STRIP_TAGS.sub('', line).strip()
                    if is_list_item:
                        clean_text = "• " + clean_text
                        
                    if clean_text or bg_color:
                        font_style = self._get_font(f_family, f_size, f_weight, zs, underline=is_underline)
                        
                        temp_txt = self.canvas.create_text(pad_x, current_y, text=clean_text if clean_text else " ", font=font_style, width=w-(30*zs))
                        bbox = self.canvas.bbox(temp_txt)
                        self.canvas.delete(temp_txt)
                        
                        if bbox:
                            if bg_color:
                                block_tags = ('<header', '<footer', '<section', '<article', '<main', '<aside', '<div', '<p', '<h1', '<h2', '<h3', '<h4', '<ul', '<ol')
                                is_block = any(t in lower_line for t in block_tags)
                                
                                if is_block: 
                                    rect_x2 = x + w - (15*zs) 
                                else: 
                                    rect_x2 = bbox[2] + (4*zs) 
                                    
                                bg_pad = 4 * zs
                                self.canvas.create_rectangle(pad_x - bg_pad, bbox[1] - (2*zs), rect_x2, bbox[3] + (2*zs), fill=self.blend_color(bg_color, blended_bg, content_opacity), outline=self.blend_color(bg_color, blended_bg, content_opacity), tags=node_tags)
                            
                            if clean_text:
                                self.canvas.create_text(pad_x, current_y, anchor=tk.NW, text=clean_text, fill=self.blend_color(text_color, blended_bg, content_opacity), font=font_style, width=w-(30*zs), tags=node_tags)
                            
                            current_y = bbox[3] + (4*zs)
                    else:
                        current_y += 10 * zs
                        
            elif n["type"] == "Диаграмма":
                lines = display_content.split("\n")
                data = []
                for l in lines:
                    parts = RE_CHART_SPLIT.split(l)
                    if len(parts) >= 2:
                        try: 
                            data.append((parts[0].strip(), float(parts[1].strip())))
                        except: 
                            pass
                
                if not data:
                    self.canvas.create_text(cx, cy, text="Нет данных", fill=self.blend_color("gray", blended_bg, content_opacity), tags=node_tags)
                else:
                    max_val = max((v for k, v in data), default=0)
                    max_val = max(max_val, 1)
                    # Предотвращение отрицательных размеров диаграммы при сильном сжатии узла
                    chart_w = max(20 * zs, w - (40*zs))
                    chart_h = max(20 * zs, h - header_h - (35*zs))
                    bar_w = chart_w / len(data)
                    chart_colors = ("#0078D4", "#10B981", "#F59E0B", "#EF4444", "#8B5CF6", "#EC4899", "#06B6D4")
                    
                    self.canvas.create_line(pad_x, pad_y + chart_h, pad_x + chart_w, pad_y + chart_h, fill=self.blend_color("#CCCCCC" if not is_dark_bg else "#5F5F5F", blended_bg, content_opacity), tags=node_tags)
                    self.canvas.create_line(pad_x, pad_y, pad_x, pad_y + chart_h, fill=self.blend_color("#CCCCCC" if not is_dark_bg else "#5F5F5F", blended_bg, content_opacity), tags=node_tags)
                    
                    font_lbl = self._get_font("Segoe UI", 7, zs=zs)
                    font_val = self._get_font("Segoe UI", 8, "bold", zs)
                    
                    for i, (lbl, val) in enumerate(data):
                        b_height = (val / max_val) * chart_h
                        b_x1 = pad_x + i * bar_w + (5*zs)
                        b_y1 = pad_y + chart_h - b_height
                        b_x2 = b_x1 + bar_w - (10*zs)
                        b_y2 = pad_y + chart_h
                        c = chart_colors[i % len(chart_colors)]
                        
                        bl_c = self.blend_color(c, blended_bg, content_opacity)
                        self.canvas.create_rectangle(b_x1, b_y1, b_x2, b_y2, fill=bl_c, outline=bl_c, tags=node_tags)
                        self.canvas.create_text(b_x1 + (b_x2-b_x1)/2, b_y2 + (8*zs), text=lbl[:7]+(".." if len(lbl)>7 else ""), font=font_lbl, fill=blended_secondary_color, tags=node_tags)
                        self.canvas.create_text(b_x1 + (b_x2-b_x1)/2, b_y1 - (8*zs), text=str(val), font=font_val, fill=blended_text_color, tags=node_tags)

            elif n["type"] == "Секторная диаграмма":
                lines = display_content.split("\n")
                data = []
                for l in lines:
                    parts = RE_CHART_SPLIT.split(l)
                    if len(parts) >= 2:
                        try: 
                            data.append((parts[0].strip(), float(parts[1].strip())))
                        except: 
                            pass
                
                total = sum(v for k, v in data)
                if total <= 0:
                    self.canvas.create_text(cx, cy, text="Нет данных", fill=self.blend_color("gray", blended_bg, content_opacity), tags=node_tags)
                else:
                    r = max(10 * zs, min(w, h - header_h) / 2 - (25*zs))
                    pie_cx = pad_x + r
                    pie_cy = pad_y + r + (10*zs)
                    chart_colors = ("#0078D4", "#10B981", "#F59E0B", "#EF4444", "#8B5CF6", "#EC4899", "#06B6D4", "#F43F5E", "#14B8A6")
                    
                    start_ang = 0
                    font_leg = self._get_font("Segoe UI", 8, zs=zs)
                    for i, (lbl, val) in enumerate(data):
                        extent = (val / total) * 360
                        c = chart_colors[i % len(chart_colors)]
                        bl_c = self.blend_color(c, blended_bg, content_opacity)
                        self.canvas.create_arc(pie_cx-r, pie_cy-r, pie_cx+r, pie_cy+r, start=start_ang, extent=extent, fill=bl_c, outline="white" if not is_dark_bg else "#2D2D2D", tags=node_tags)
                        
                        leg_x = pie_cx + r + (15*zs)
                        leg_y = pad_y + i*(18*zs) + (10*zs)
                        
                        if leg_y + (10*zs) <= y + h - (5*zs):
                            self.canvas.create_rectangle(leg_x, leg_y, leg_x+(10*zs), leg_y+(10*zs), fill=bl_c, outline=self.blend_color("gray", blended_bg, content_opacity), tags=node_tags)
                            percent = int(val/total*100)
                            self.canvas.create_text(leg_x+(15*zs), leg_y, anchor=tk.NW, text=f"{lbl} ({percent}%)", font=font_leg, fill=blended_text_color, tags=node_tags)
                        
                        start_ang += extent
                
            elif n["type"] == "Изображение":
                fpath = n.get("filepath", "")
                img_data = self.get_tk_image(fpath, target_scale=zs)
                if img_data:
                    img_x_offset = pad_x - (5*zs)
                    if isinstance(img_data, dict):
                        if img_data.get("animated"):
                            img_obj = img_data["frames"][0]
                            item_id = self.canvas.create_image(img_x_offset, pad_y, anchor=tk.NW, image=img_obj, tags=node_tags)
                            cache_key = f"{fpath}_{round(zs, 2)}"
                            self.animated_items[node_id] = {"item_id": item_id, "filepath": fpath, "cache_key": cache_key}
                        else:
                            self.canvas.create_image(img_x_offset, pad_y, anchor=tk.NW, image=img_data["img"], tags=node_tags)
                    else:
                        self.canvas.create_image(img_x_offset, pad_y, anchor=tk.NW, image=img_data, tags=node_tags)
                        
                    self.canvas.create_text(cx, y + h - (15*zs), text=display_content, fill=blended_secondary_color, font=self._get_font("Segoe UI", 9, "italic", zs), tags=node_tags)
                else:
                    self.canvas.create_rectangle(pad_x, pad_y, x+w-(15*zs), y+h-(35*zs), fill=self.blend_color("#FEE2E2" if not is_dark_bg else "#7F1D1D", blended_bg, content_opacity), outline=self.blend_color("#EF4444", blended_bg, content_opacity), tags=node_tags)
                    self.canvas.create_text(cx, cy-(5*zs), text="ОШИБКА ЗАГРУЗКИ", fill=self.blend_color("#991B1B" if not is_dark_bg else "#FCA5A5", blended_bg, content_opacity), justify=tk.CENTER, font=self._get_font("Segoe UI", 9, "bold", zs), tags=node_tags)
                    
            else: 
                # Стандартный вывод текстового содержимого с автоподгонкой и усечением в заданных рамках
                max_w = w - (30 * zs)
                max_h = h - header_h - (15 * zs)
                wrapped_lines, f_size = self.fit_text_to_box(display_content, "Segoe UI", max_w, max_h, zs)
                
                line_h = f_size * 1.35 * zs
                curr_y = pad_y
                font_style = self._get_font("Segoe UI", f_size, zs=zs)
                for line in wrapped_lines:
                    self.canvas.create_text(pad_x, curr_y, anchor=tk.NW, text=line, fill=blended_text_color, font=font_style, tags=node_tags)
                    curr_y += line_h

        # Отрисовка утонченного углового маркера изменения пропорций (ресайзера)
        if node_id == self.selected_node and not self.view_mode.get():
            hx, hy = x + w, y + h
            bl_resizer = self.blend_color("#0078D4", blended_bg, content_opacity)
            
            # Векторный уголок из трех линий для профессионального вида
            self.canvas.create_line(hx - 12*zs, hy, hx, hy, fill=bl_resizer, width=1.5*zs, tags=node_tags + ("resize_handle",))
            self.canvas.create_line(hx, hy - 12*zs, hx, hy, fill=bl_resizer, width=1.5*zs, tags=node_tags + ("resize_handle",))
            self.canvas.create_line(hx - 9*zs, hy - 2*zs, hx - 2*zs, hy - 9*zs, fill=bl_resizer, width=1.2*zs, tags=node_tags + ("resize_handle",))
            self.canvas.create_line(hx - 6*zs, hy - 2*zs, hx - 2*zs, hy - 6*zs, fill=bl_resizer, width=1.2*zs, tags=node_tags + ("resize_handle",))

    def get_tk_image(self, filepath, target_scale=1.0):
        cache_key = f"{filepath}_{round(target_scale, 2)}"
        if cache_key in self.image_cache:
            return self.image_cache[cache_key]
            
        if not os.path.exists(filepath):
            return None
        
        try:
            if HAS_PIL:
                if filepath not in self.source_image_cache:
                    img = Image.open(filepath)
                    if getattr(img, "is_animated", False):
                        extracted = []
                        for frame in ImageSequence.Iterator(img):
                            extracted.append(frame.copy().convert("RGBA"))
                        self.source_image_cache[filepath] = {
                            "animated": True,
                            "frames": extracted
                        }
                    else:
                        self.source_image_cache[filepath] = {
                            "animated": False,
                            "img": img.copy()
                        }
                
                source_data = self.source_image_cache[filepath]
                base_w, base_h = 350, 350
                target_w = max(1, int(base_w * target_scale))
                target_h = max(1, int(base_h * target_scale))
                
                if source_data["animated"]:
                    num_frames = len(source_data["frames"])
                    
                    f_copy = source_data["frames"][0].copy()
                    f_copy.thumbnail((target_w, target_h), Image.Resampling.LANCZOS)
                    tk_img = ImageTk.PhotoImage(f_copy)
                    
                    frames = [None] * num_frames
                    frames[0] = tk_img
                    
                    self.image_cache[cache_key] = {
                        "animated": True, 
                        "frames": frames, 
                        "target_w": target_w,
                        "target_h": target_h,
                        "w": tk_img.width(), 
                        "h": tk_img.height()
                    }
                else:
                    img = source_data["img"].copy()
                    img.thumbnail((target_w, target_h), Image.Resampling.LANCZOS)
                    tk_img = ImageTk.PhotoImage(img)
                    self.image_cache[cache_key] = {
                        "animated": False, "img": tk_img, 
                        "w": tk_img.width(), "h": tk_img.height()
                    }
            else:
                tk_img = tk.PhotoImage(file=filepath)
                self.image_cache[cache_key] = tk_img
                
            return self.image_cache[cache_key]
        except Exception as e:
            print(f"Ошибка загрузки растра {filepath}: {e}")
            return None

    def save_state(self, initial=False):
        state = {"nodes": copy.deepcopy(self.nodes), "edges": copy.deepcopy(self.edges), "node_counter": self.node_counter}
        self.history = self.history[:self.history_index + 1]
        self.history.append(state)
        self.history_index += 1
        
        if not initial:
            self.is_modified = True
            self.update_window_title()

    def undo(self):
        if self.view_mode.get(): 
            return
        if self.history_index > 0:
            self.history_index -= 1
            self.restore_state()
            self.update_status("Действие отменено")
            self.is_modified = True
            self.update_window_title()

    def redo(self):
        if self.view_mode.get(): 
            return
        if self.history_index < len(self.history) - 1:
            self.history_index += 1
            self.restore_state()
            self.update_status("Действие повторено")
            self.is_modified = True
            self.update_window_title()

    def restore_state(self):
        state = copy.deepcopy(self.history[self.history_index])
        self.nodes, self.edges, self.node_counter = state["nodes"], state["edges"], state["node_counter"]
        self.selected_node = self.connecting_from = self.resizing_node = None
        self.selected_edge = None
        self.render()
        self.update_navigator_list()

    def new_file(self):
        if self.is_modified:
            result = messagebox.askyesnocancel("Сохранить изменения?", "Сохранить текущую схему перед созданием новой?")
            if result is True:
                if not self.save_file():
                    return
            elif result is None:
                return

        self._stop_all_playback()
        self.nodes, self.edges, self.node_counter, self.history = {}, [], 0, []
        self.history_index = -1
        self.offset_x, self.offset_y = 0, 0
        self.zoom_level = 1.0
        self.zoom_label.config(text="100%")
        self.image_cache.clear()
        self.source_image_cache.clear()
        self.anim_ticks.clear()
        
        self.current_filename = None
        self.is_modified = False
        
        self.save_state(initial=True)
        self.render()
        self.update_navigator_list()
        self.update_status("Новая схема создана")

    def save_file(self):
        filepath = filedialog.asksaveasfilename(
            defaultextension=".json", 
            filetypes=[("Схема MindsMap", "*.json")],
            initialfile=os.path.basename(self.current_filename) if self.current_filename else "Схема1"
        )
        if filepath:
            try:
                data_to_save = {
                    "nodes": self.nodes, "edges": self.edges, "counter": self.node_counter,
                    "view": {"offset_x": self.offset_x, "offset_y": self.offset_y, "zoom": self.zoom_level}
                }
                with open(filepath, 'w', encoding='utf-8') as f: 
                    json.dump(data_to_save, f, ensure_ascii=False, indent=2)
                    
                self.current_filename = filepath
                self.is_modified = False
                self.update_window_title()
                
                self.update_status(f"Схема сохранена: {os.path.basename(filepath)}")
                return True 
            except Exception as e:
                messagebox.showerror("Ошибка", f"Не удалось сохранить файл:\n{e}")
                return False
        return False

    def load_file(self):
        if self.is_modified:
            result = messagebox.askyesnocancel("Сохранить изменения?", "Сохранить текущие изменения перед загрузкой?")
            if result is True:
                if not self.save_file(): 
                    return
            elif result is None:
                return

        filepath = filedialog.askopenfilename(filetypes=[("Схема MindsMap", "*.json")])
        if filepath:
            try:
                with open(filepath, 'r', encoding='utf-8') as f: 
                    data = json.load(f)
                self.nodes = data.get("nodes", {})
                self.node_counter = data.get("counter", 0)
                
                raw_edges = data.get("edges", [])
                self.edges = [e if len(e) >= 3 else [e[0], e[1], 1] for e in raw_edges]
                
                for n_id, n in self.nodes.items():
                    if "scale" not in n: 
                        n["scale"] = 1.0
                    if n["type"] == "Часы" and "clock_time" not in n:
                        n["clock_time"] = time.time()
                        n["is_running"] = True
                        n["last_update"] = time.time()
                    if n["type"] == "Магнитола":
                        n.setdefault("playlist", [])
                        n.setdefault("track_idx", 0)
                        n.setdefault("volume", 80)
                        n["is_playing"] = False
                        n["play_started_at"] = None
                        n.setdefault("elapsed", 0.0)
                    
                    if "hide_border" not in n: 
                        n["hide_border"] = False
                    if "hide_content" not in n: 
                        n["hide_content"] = False
                    
                    def_colors = self.colors.get(n["type"], self.colors["Текст"])
                    if "border_color" not in n: 
                        n["border_color"] = def_colors["border"]
                    if "bg_color" not in n: 
                        n["bg_color"] = def_colors["bg"]
                        
                    if "border_opacity" not in n: 
                        n["border_opacity"] = 1.0
                    if "bg_opacity" not in n: 
                        n["bg_opacity"] = 1.0
                    if "content_opacity" not in n: 
                        n["content_opacity"] = 1.0
                    if "lock_aspect_ratio" not in n:
                        n["lock_aspect_ratio"] = False
                    if "aspect_ratio" not in n:
                        n["aspect_ratio"] = n["w"] / n["h"] if n.get("h", 0) > 0 else 1.33
                
                view_data = data.get("view", {})
                self.offset_x = view_data.get("offset_x", 0)
                self.offset_y = view_data.get("offset_y", 0)
                self.zoom_level = view_data.get("zoom", 1.0)
                
                self.zoom_label.config(text=f"{int(self.zoom_level * 100)}%")
                self.image_cache.clear()
                self.source_image_cache.clear()
                
                self.current_filename = filepath
                self.is_modified = False
                self.update_window_title()
                
                self.save_state(initial=True)
                self.render()
                self.update_navigator_list()
                self.update_status(f"Схема загружена: {os.path.basename(filepath)}")
            except Exception as e:
                messagebox.showerror("Ошибка", f"Не удалось прочитать файл:\n{e}")

    def export_to_image(self):
        if not HAS_PIL:
            messagebox.showwarning("Библиотека отсутствует", "Для экспорта растра требуется установить Pillow:\npip install Pillow")
            return
            
        filepath = filedialog.asksaveasfilename(defaultextension=".png", filetypes=[("Изображение PNG", "*.png")])
        if not filepath: 
            return
        
        self.update_idletasks()
        x0 = self.canvas.winfo_rootx()
        y0 = self.canvas.winfo_rooty()
        x1 = x0 + self.canvas.winfo_width()
        y1 = y0 + self.canvas.winfo_height()
        
        try:
            img = ImageGrab.grab(bbox=(x0, y0, x1, y1))
            img.save(filepath, 'PNG')
            self.update_status(f"Экспортировано: {os.path.basename(filepath)}")
            messagebox.showinfo("Готово", "Изображение успешно сгенерировано.")
        except Exception as e:
            messagebox.showerror("Ошибка экспорта", f"Не удалось выполнить рендеринг в файл:\n{e}")

if __name__ == "__main__":
    app = DiagramPlanner()
    app.bind("<Configure>", lambda e: app.schedule_render() if e.widget == app else None)
    app.mainloop()