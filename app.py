import tkinter as tk
from tkinter import ttk, filedialog, colorchooser, messagebox
import os
import json
import io
import zipfile
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
import numpy as np
import pandas as pd
import matplotlib
import tkinter.font as tkfont

matplotlib.use("TkAgg")
from matplotlib.figure import Figure
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import matplotlib.pyplot as plt


class CollapsibleFrame(ttk.Frame):
    def __init__(self, parent, text="", collapsed=True, *args, **kwargs):
        super().__init__(parent, *args, **kwargs)
        self.collapsed = collapsed
        self.text = text

        self.header = ttk.Frame(self)
        self.header.pack(fill=tk.X)

        self.toggle_btn = ttk.Button(self.header, text="+" if collapsed else "−", width=3, command=self.toggle)
        self.toggle_btn.pack(side=tk.LEFT)

        self.title_lbl = ttk.Label(self.header, text=text, font=("TkDefaultFont", 10, "bold"))
        self.title_lbl.pack(side=tk.LEFT, padx=5)

        self.content = ttk.Frame(self)
        if not collapsed:
            self.content.pack(fill=tk.X, padx=10, pady=5)

    def toggle(self):
        if self.collapsed:
            self.content.pack(fill=tk.X, padx=10, pady=5)
            self.toggle_btn.configure(text="−")
            self.collapsed = False
        else:
            self.content.pack_forget()
            self.toggle_btn.configure(text="+")
            self.collapsed = True


class TensileApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Tensile Results Visualizer")
        self.geometry("1400x900")

        # Данные
        self.sheets_data = {}
        self.sample_states = {}
        self.sample_colors = {}
        self.sample_linewidths = {}
        self.sample_linestyles = {}
        self.sample_markers = {}
        self.sample_file = {}
        self.sample_widgets = {}
        self.files = {}
        self.file_states = {}
        self.sample_axis_pairs = {}
        self.file_S0 = {}
        self.file_samples_order = {}
        self.tooltip = None
        self.graph_hover_cid = None
        self.columns = []
        self.x_col = None
        self.y_col = None
        self.plot_timer = None  # Таймер для отложенной перерисовки графика

        # Настройки графика
        self.sort_mode = tk.StringVar(value="name")
        self.sort_order = tk.StringVar(value="asc")
        self.scale_mode = tk.StringVar(value="linear")
        self.grid_on = tk.BooleanVar(value=True)
        self.show_legend = tk.BooleanVar(value=True)
        self.xmin = tk.StringVar(value="0")
        self.xmax = tk.StringVar()
        self.ymin = tk.StringVar(value="0")
        self.ymax = tk.StringVar()
        self.avg_degree = tk.IntVar(value=7)
        self.avg_on = tk.BooleanVar(value=False)
        self.avg_alpha = tk.StringVar(value="0.9")
        self.sample_alpha = tk.StringVar(value="0.2")

        # Настройки текста графика
        self.text_font = tk.StringVar(value="sans-serif")
        self.text_size = tk.IntVar(value=10)
        self.text_bold = tk.BooleanVar(value=False)
        self.text_italic = tk.BooleanVar(value=False)
        self.text_color = tk.StringVar(value="black")

        # Настройки шрифтов
        self.favorite_fonts = ["Arial", "Sans Serif", "Times New Roman", "Helvetica", "Calibri", "Verdana"]
        system_fonts = sorted({f for f in tkfont.families() if not f.startswith("@")})

        self.available_fonts = [f for f in self.favorite_fonts if f in system_fonts]
        if self.available_fonts:
            self.available_fonts.append("────────")
        self.available_fonts.extend([f for f in system_fonts if f not in self.favorite_fonts])

        self.font_sizes = [str(i) for i in range(6, 33)]

        self.font_gen_fam = tk.StringVar(value="Arial")
        self.font_gen_size = tk.StringVar(value="10")

        self.font_ax_fam = tk.StringVar(value="Arial")
        self.font_ax_size = tk.StringVar(value="10")
        self.font_ax_color = tk.StringVar(value="black")
        self.font_ax_bold = tk.BooleanVar(value=False)
        self.font_ax_italic = tk.BooleanVar(value=False)

        self.font_tick_fam = tk.StringVar(value="Arial")
        self.font_tick_size = tk.StringVar(value="8")
        self.font_tick_color = tk.StringVar(value="black")
        self.font_tick_bold = tk.BooleanVar(value=False)
        self.font_tick_italic = tk.BooleanVar(value=False)

        self.font_leg_fam = tk.StringVar(value="Arial")
        self.font_leg_size = tk.StringVar(value="9")
        self.font_leg_color = tk.StringVar(value="black")
        self.font_leg_bold = tk.BooleanVar(value=False)
        self.font_leg_italic = tk.BooleanVar(value=False)

        # Трассировка для автоматического обновления графика
        for var in [self.font_ax_fam, self.font_ax_size, self.font_tick_fam,
                    self.font_tick_size, self.font_leg_fam, self.font_leg_size]:
            var.trace_add("write", lambda *args: self._on_individual_font_change())


        self.avg_alpha.trace_add("write", lambda *args: self.plot_data())
        self.sample_alpha.trace_add("write", lambda *args: self.plot_data())

        self.file_avg_colors = {}
        self.file_avg_styles = {}
        self.file_avg_widths = {}

        self._build_ui()

    def _safe_font_family(self, family):
        fonts = set(tkfont.families())
        if family in fonts:
            return family
        for fallback in ("Arial", "Sans Serif", "DejaVu Sans", "Helvetica", "Calibri", "Verdana"):
            if fallback in fonts:
                return fallback
        return "sans-serif"

    def _font_style_dict(self, fam_var, size_var, color_var=None, bold_var=None, italic_var=None):
        d = {
            "family": self._safe_font_family(fam_var.get()),
            "size": int(size_var.get()) if str(size_var.get()).strip() else 10,
            "weight": "bold" if bold_var and bold_var.get() else "normal",
            "style": "italic" if italic_var and italic_var.get() else "normal",
        }
        if color_var is not None:
            d["color"] = color_var.get() or "black"
        return d

    def _schedule_plot(self, *args):
        """Отложенная перерисовка графика для защиты от зависаний при ручном вводе"""
        if self.plot_timer:
            self.after_cancel(self.plot_timer)
        self.plot_timer = self.after(300, self.plot_data)

    def _build_ui(self):
        style = ttk.Style()
        style.configure("File.TCheckbutton", font=("TkDefaultFont", 10, "bold"))

        main = ttk.Panedwindow(self, orient=tk.HORIZONTAL)
        main.pack(fill=tk.BOTH, expand=True)

        left = ttk.Frame(main, padding=10)
        right = ttk.Frame(main, padding=10)
        main.add(left, weight=1)
        main.add(right, weight=3)

        # 1. Импорт и основные оси
        top_controls = ttk.LabelFrame(left, text="Импорт и оси")
        top_controls.pack(fill=tk.X, pady=(0, 10))

        open_btn = ttk.Button(top_controls, text="Добавить .xls/.xlsx", command=self.load_files)
        open_btn.grid(row=0, column=0, padx=5, pady=5, sticky="w")
        edit_btn = ttk.Button(top_controls, text="Изменить данные", command=self.open_edit_data_window)
        edit_btn.grid(row=0, column=1, padx=5, pady=5, sticky="w")

        ttk.Label(top_controls, text="Ось X").grid(row=1, column=0, padx=5, pady=5, sticky="w")
        self.x_select = ttk.Combobox(top_controls, values=self.columns, state="readonly")
        self.x_select.grid(row=1, column=1, columnspan=2, padx=5, pady=5, sticky="we")
        self.x_select.bind("<<ComboboxSelected>>", lambda e: self.plot_data())

        ttk.Label(top_controls, text="Ось Y").grid(row=2, column=0, padx=5, pady=5, sticky="w")
        self.y_select = ttk.Combobox(top_controls, values=self.columns, state="readonly")
        self.y_select.grid(row=2, column=1, columnspan=2, padx=5, pady=5, sticky="we")
        self.y_select.bind("<<ComboboxSelected>>", lambda e: self.plot_data())

        conv_n_btn = ttk.Button(top_controls, text="В Ньютоны", command=self.convert_to_newtons)
        conv_n_btn.grid(row=3, column=0, padx=5, pady=5, sticky="w")
        conv_mpa_btn = ttk.Button(top_controls, text="В МПа", command=self.convert_to_mpa)
        conv_mpa_btn.grid(row=3, column=1, padx=5, pady=5, sticky="w")
        top_controls.columnconfigure(1, weight=1)

        # 2. Шрифты (сворачиваемая)
        self.fontframecollapsible = CollapsibleFrame(left, text="Настройка текста", collapsed=True)
        self.fontframecollapsible.pack(fill=tk.X, pady=5)
        fframe = self.fontframecollapsible.content

        def createfontrow(parent, label, famvar, sizevar, row, colorvar, boldvar, italicvar, isgen=False):
            ttk.Label(parent, text=label).grid(row=row, column=0, padx=5, pady=2, sticky="w")

            fcb = ttk.Combobox(parent, textvariable=famvar, values=self.available_fonts, width=18, state="readonly")
            fcb.grid(row=row, column=1, padx=2, pady=2, sticky="we")

            scb = ttk.Combobox(parent, textvariable=sizevar, values=self.font_sizes, width=4, state="readonly")
            scb.grid(row=row, column=2, padx=2, pady=2, sticky="w")

            def pick_color():
                col = colorchooser.askcolor(title=f"Цвет: {label}", initialcolor=colorvar.get())[1]
                if col:
                    colorvar.set(col)
                    self.plot_data()

            ttk.Button(parent, text="Цвет", command=pick_color).grid(row=row, column=3, padx=2, pady=2, sticky="w")
            ttk.Checkbutton(parent, text="Ж", variable=boldvar, command=self.plot_data).grid(row=row, column=4, padx=2,
                                                                                             pady=2)
            ttk.Checkbutton(parent, text="К", variable=italicvar, command=self.plot_data).grid(row=row, column=5, padx=2,
                                                                                               pady=2)


            if isgen:
                def _apply_general_font(self):
                    fam = self.font_gen_fam.get()
                    size = self.font_gen_size.get()

                    if fam and fam != "...":
                        self.font_ax_fam.set(fam)
                        self.font_tick_fam.set(fam)
                        self.font_leg_fam.set(fam)

                    if size and size != "...":
                        self.font_ax_size.set(size)
                        self.font_tick_size.set(size)
                        self.font_leg_size.set(size)

                    self.plot_data()
                fcb.bind("<<ComboboxSelected>>", lambda e: self._apply_general_font())
                scb.bind("<<ComboboxSelected>>", lambda e: self._apply_general_font())

        createfontrow(fframe, "Общий шрифт", self.font_gen_fam, self.font_gen_size, 0, self.text_color, self.text_bold,
                      self.text_italic, tk.BooleanVar(value=False))
        ttk.Separator(fframe, orient=tk.HORIZONTAL).grid(row=1, column=0, columnspan=7, sticky="we", pady=5)

        createfontrow(fframe, "Подписи осей", self.font_ax_fam, self.font_ax_size, 2, self.font_ax_color, self.font_ax_bold,
                      self.font_ax_italic)
        createfontrow(fframe, "Шкала (тики)", self.font_tick_fam, self.font_tick_size, 3, self.font_tick_color,
                      self.font_tick_bold, self.font_tick_italic)
        createfontrow(fframe, "Легенда", self.font_leg_fam, self.font_leg_size, 4, self.font_leg_color, self.font_leg_bold,
                      self.font_leg_italic)

        fframe.columnconfigure(1, weight=1)

        # 3. Сортировка (сворачиваемая)
        self.sort_frame_collapsible = CollapsibleFrame(left, text="Сортировка", collapsed=True)
        self.sort_frame_collapsible.pack(fill=tk.X, pady=5)
        sort_frame = self.sort_frame_collapsible.content

        ttk.Label(sort_frame, text="Режим").grid(row=0, column=0, padx=5, pady=5, sticky="w")
        sort_mode = ttk.Combobox(sort_frame, state="readonly", values=["name", "max_y"], textvariable=self.sort_mode)
        sort_mode.grid(row=0, column=1, padx=5, pady=5, sticky="we")
        ttk.Label(sort_frame, text="Порядок").grid(row=1, column=0, padx=5, pady=5, sticky="w")
        sort_order = ttk.Combobox(sort_frame, state="readonly", values=["asc", "desc"], textvariable=self.sort_order)
        sort_order.grid(row=1, column=1, padx=5, pady=5, sticky="we")
        sort_btn = ttk.Button(sort_frame, text="Применить", command=self.apply_sort)
        sort_btn.grid(row=2, column=0, padx=5, pady=5, sticky="w")
        sort_frame.columnconfigure(1, weight=1)

        # 4. Оси и лимиты (сворачиваемая)
        self.axes_frame_collapsible = CollapsibleFrame(left, text="Границы осей", collapsed=True)
        self.axes_frame_collapsible.pack(fill=tk.X, pady=5)
        axes_frame = self.axes_frame_collapsible.content

        ttk.Label(axes_frame, text="X min").grid(row=0, column=0, padx=5, pady=2, sticky="w")
        ttk.Entry(axes_frame, textvariable=self.xmin).grid(row=0, column=1, padx=5, pady=2, sticky="we")
        ttk.Label(axes_frame, text="X max").grid(row=1, column=0, padx=5, pady=2, sticky="w")
        ttk.Entry(axes_frame, textvariable=self.xmax).grid(row=1, column=1, padx=5, pady=2, sticky="we")
        ttk.Label(axes_frame, text="Y min").grid(row=2, column=0, padx=5, pady=2, sticky="w")
        ttk.Entry(axes_frame, textvariable=self.ymin).grid(row=2, column=1, padx=5, pady=2, sticky="we")
        ttk.Label(axes_frame, text="Y max").grid(row=3, column=0, padx=5, pady=2, sticky="w")
        ttk.Entry(axes_frame, textvariable=self.ymax).grid(row=3, column=1, padx=5, pady=2, sticky="we")
        ttk.Label(axes_frame, text="Масштаб").grid(row=4, column=0, padx=5, pady=2, sticky="w")
        ttk.Combobox(axes_frame, state="readonly", values=["linear", "log"], textvariable=self.scale_mode).grid(row=4,
                                                                                                                column=1,
                                                                                                                padx=5,
                                                                                                                pady=2,
                                                                                                                sticky="we")
        ttk.Checkbutton(axes_frame, text="Сетка", variable=self.grid_on, command=self.plot_data).grid(row=5, column=0,
                                                                                                      padx=5, pady=2,
                                                                                                      sticky="w")
        ttk.Checkbutton(axes_frame, text="Легенда", variable=self.show_legend, command=self.plot_data).grid(row=5,
                                                                                                            column=1,
                                                                                                            padx=5,
                                                                                                            pady=2,
                                                                                                            sticky="w")

        ttk.Button(axes_frame, text="Сбросить масштаб", command=self.reset_scale).grid(row=6, column=0, columnspan=2,
                                                                                       sticky="we", pady=5)

        self.scale_mode.trace_add("write", lambda *args: self.plot_data())
        self.xmin.trace_add("write", self._schedule_plot)
        self.xmax.trace_add("write", self._schedule_plot)
        self.ymin.trace_add("write", self._schedule_plot)
        self.ymax.trace_add("write", self._schedule_plot)
        axes_frame.columnconfigure(1, weight=1)

        # 5. Усреднение (сворачиваемая)
        self.avg_frame_collapsible = CollapsibleFrame(left, text="Усредненный график", collapsed=True)
        self.avg_frame_collapsible.pack(fill=tk.X, pady=5)
        avg_frame = self.avg_frame_collapsible.content

        ttk.Label(avg_frame, text="Степень полинома").grid(row=0, column=0, padx=5, pady=2, sticky="w")
        ttk.Spinbox(avg_frame, from_=1, to=20, textvariable=self.avg_degree, width=5, command=self.plot_data).grid(
            row=0, column=1, padx=5, pady=2, sticky="w")
        ttk.Label(avg_frame, text="Alpha (линии)").grid(row=1, column=0, padx=5, pady=2, sticky="w")
        ttk.Entry(avg_frame, textvariable=self.sample_alpha, width=5).grid(row=1, column=1, padx=5, pady=2, sticky="w")
        ttk.Label(avg_frame, text="Alpha (среднее)").grid(row=2, column=0, padx=5, pady=2, sticky="w")
        ttk.Entry(avg_frame, textvariable=self.avg_alpha, width=5).grid(row=2, column=1, padx=5, pady=2, sticky="w")
        ttk.Checkbutton(avg_frame, text="Построить среднее", variable=self.avg_on, command=self.plot_data).grid(row=3,
                                                                                                                column=0,
                                                                                                                columnspan=2,
                                                                                                                padx=5,
                                                                                                                pady=2,
                                                                                                                sticky="w")

        self.avg_styles_container = ttk.Frame(avg_frame)
        self.avg_styles_container.grid(row=4, column=0, columnspan=2, sticky="we", pady=5)
        avg_frame.columnconfigure(1, weight=1)

        # 6. Сохранение (сворачиваемая)
        self.save_frame_collapsible = CollapsibleFrame(left, text="Сохранение", collapsed=True)
        self.save_frame_collapsible.pack(fill=tk.X, pady=5)
        save_frame = self.save_frame_collapsible.content

        ttk.Label(save_frame, text="DPI").grid(row=0, column=0, padx=5, pady=2, sticky="w")
        self.save_dpi = tk.StringVar(value="100")
        ttk.Entry(save_frame, textvariable=self.save_dpi).grid(row=0, column=1, padx=5, pady=2, sticky="we")
        ttk.Label(save_frame, text="Ширина").grid(row=1, column=0, padx=5, pady=2, sticky="w")
        self.save_w = tk.StringVar(value="6")
        ttk.Entry(save_frame, textvariable=self.save_w).grid(row=1, column=1, padx=5, pady=2, sticky="we")
        ttk.Label(save_frame, text="Высота").grid(row=2, column=0, padx=5, pady=2, sticky="w")
        self.save_h = tk.StringVar(value="4")
        ttk.Entry(save_frame, textvariable=self.save_h).grid(row=2, column=1, padx=5, pady=2, sticky="we")
        ttk.Button(save_frame, text="Сохранить график", command=self.save_plot).grid(row=3, column=0, padx=5, pady=2,
                                                                                     sticky="w")
        ttk.Button(save_frame, text="Сохранить сессию", command=self.save_session).grid(row=3, column=1, padx=5, pady=2,
                                                                                        sticky="e")
        ttk.Button(save_frame, text="Загрузить сессию", command=self.load_session).grid(row=4, column=1, padx=5, pady=2,
                                                                                        sticky="e")
        save_frame.columnconfigure(1, weight=1)

        # 7. Управление графиками и образцами (сворачиваемая)
        self.samples_frame_collapsible = CollapsibleFrame(left, text="Управление графиками и образцами",
                                                          collapsed=False)
        self.samples_frame_collapsible.pack(fill=tk.BOTH, expand=True, pady=5)
        samples_main_frame = self.samples_frame_collapsible.content

        # Панель инструментов для управления файлами
        top_bar = ttk.Frame(samples_main_frame)
        top_bar.pack(fill=tk.X, pady=(0, 5))

        self.files_menu_btn = ttk.Menubutton(top_bar, text="Фильтр файлов")
        self.files_menu = tk.Menu(self.files_menu_btn, tearoff=0)
        self.files_menu_btn["menu"] = self.files_menu
        self.files_menu_btn.pack(side=tk.LEFT, padx=2)

        self.file_to_delete = tk.StringVar()
        self.file_delete_combo = ttk.Combobox(top_bar, state="readonly", textvariable=self.file_to_delete, width=15)
        self.file_delete_combo.pack(side=tk.LEFT, padx=2)
        ttk.Button(top_bar, text="Удалить файл", command=self._delete_selected_file).pack(side=tk.LEFT, padx=2)
        ttk.Button(top_bar, text="Сброс цветов", command=self._reset_colors).pack(side=tk.RIGHT, padx=2)

        # Контейнер для списка образцов
        canvas = tk.Canvas(samples_main_frame, borderwidth=0)
        vscroll = ttk.Scrollbar(samples_main_frame, orient=tk.VERTICAL, command=canvas.yview)
        self.samples_container_frame = ttk.Frame(canvas)
        self.samples_container_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=self.samples_container_frame, anchor="nw")
        canvas.configure(yscrollcommand=vscroll.set)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        vscroll.pack(side=tk.RIGHT, fill=tk.Y)

        # Область графика
        plot_frame = ttk.LabelFrame(right, text="График")
        plot_frame.pack(fill=tk.BOTH, expand=True, pady=(10, 0))
        self.fig = Figure(figsize=(6, 4), dpi=100)
        self.ax = self.fig.add_subplot(111)
        self.canvas = FigureCanvasTkAgg(self.fig, master=plot_frame)
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        self.hover_annot = self.ax.annotate("", xy=(0, 0), xytext=(15, 15), textcoords="offset points")
        self.hover_annot.set_visible(False)
        if self.graph_hover_cid is None:
            self.graph_hover_cid = self.canvas.mpl_connect("motion_notify_event", self._on_graph_hover)

    def _apply_general_font(self):
        """Применяет параметры общего шрифта ко всем остальным пунктам."""
        self.font_gen_fam
        fam = self.font_gen_fam.get()
        size = self.font_gen_size.get()
        if fam == "...": return

        # Отключаем трассировку временно, чтобы не вызвать циклическое обновление
        self.font_ax_fam.set(fam)
        self.font_tick_fam.set(fam)
        self.font_leg_fam.set(fam)

        if size != "...":
            self.font_ax_size.set(size)
            self.font_tick_size.set(size)
            self.font_leg_size.set(size)
        self.plot_data()

    def _on_individual_font_change(self):
        fams = {self.font_ax_fam.get(), self.font_tick_fam.get(), self.font_leg_fam.get()}
        sizes = {self.font_ax_size.get(), self.font_tick_size.get(), self.font_leg_size.get()}

        if len(fams) == 1:
            self.font_gen_fam.set(list(fams)[0])
        else:
            self.font_gen_fam.set("...")

        if len(sizes) == 1:
            self.font_gen_size.set(list(sizes)[0])
        else:
            self.font_gen_size.set("...")

        self.plot_data()

    def load_files(self):
        paths = filedialog.askopenfilenames(filetypes=[("Excel", "*.xlsx *.xls"), ("XLSX", "*.xlsx"), ("XLS", "*.xls")])
        if not paths:
            return
        self._open_progress("Загрузка файлов", len(paths))

        def worker():
            try:
                with ThreadPoolExecutor(max_workers=min(4, len(paths))) as ex:
                    futs = [ex.submit(self._read_excel_file, path) for path in paths]
                    for fut in as_completed(futs):
                        res = fut.result()

                        def merge_and_update():
                            self._merge_loaded_file_result(res)
                            self._update_progress(1, f"Загружен: {res['file_name']}")

                        self.after(0, merge_and_update())

                def finalize():
                    self._close_progress()
                    self._after_load()

                self.after(0, finalize)
            except Exception as e:
                self.after(0, lambda: (self._close_progress(), messagebox.showerror("Ошибка", str(e))))

        threading.Thread(target=worker, daemon=True).start()

    def _read_excel_file(self, path):
        fname = os.path.splitext(os.path.basename(path))[0]
        ext = os.path.splitext(path)[1].lower()
        engine = "xlrd" if ext == ".xls" else "openpyxl"
        xls = pd.ExcelFile(path, engine=engine)
        combined = {}
        axis_pairs = {}
        samples_order = []
        for sheet in xls.sheet_names:
            s_lower = str(sheet).strip().lower()
            if s_lower in ("статистика", "результаты"):
                continue
            df, axis_pair = self._parse_sheet_by_units(path, sheet, engine)
            sample_name = f"{fname}-{sheet}"
            combined[sample_name] = df
            axis_pairs[sample_name] = axis_pair
            samples_order.append(sample_name)
        results_sheet = next((s for s in xls.sheet_names if str(s).strip().lower() == "результаты"), None)
        s0_vals = []
        if results_sheet is not None:
            try:
                dfres = pd.read_excel(path, sheet_name=results_sheet, engine=engine, header=0)
                col = next((c for c in dfres.columns if str(c).strip().lower() == "s0"), None)
                if col is not None:
                    s0_vals = pd.to_numeric(dfres[col], errors="coerce").dropna().tolist()
            except Exception:
                s0_vals = []
        if samples_order:
            if len(s0_vals) > len(samples_order):
                s0_vals = s0_vals[:len(samples_order)]
            elif len(s0_vals) < len(samples_order):
                s0_vals = s0_vals + [None] * (len(samples_order) - len(s0_vals))
        return {
            "file_name": fname,
            "file_ext": ext,
            "sheets": combined,
            "axis_pairs": axis_pairs,
            "S0": s0_vals,
            "order": samples_order,
        }

    def _merge_loaded_file_result(self, res):
        self.sheets_data.update(res["sheets"])
        for sample in res["sheets"].keys():
            self.sample_file[sample] = res["file_name"]
        self.sample_axis_pairs.update(res["axis_pairs"])
        self.file_S0[res["file_name"]] = res.get("S0", [])
        self.file_samples_order[res["file_name"]] = res.get("order", [])
        if res["file_name"] not in self.files:
            self.files[res["file_name"]] = {"ext": res["file_ext"]}
            self.file_states[res["file_name"]] = tk.BooleanVar(value=True)

    def _parse_sheet_by_units(self, path, sheet, engine):
        raw = pd.read_excel(path, sheet_name=sheet, engine=engine, header=None)
        header_idx = None
        keywords = {"удлинение", "напряжение", "деформация", "сила"}
        max_scan = min(10, len(raw))
        for i in range(max_scan):
            row = [str(x).strip().lower() for x in list(raw.iloc[i].values)]
            if any(any(c.startswith(k) for k in keywords) for c in row):
                header_idx = i
                break
        if header_idx is None:
            header_idx = 0
        unit_idx = header_idx + 1 if header_idx + 1 < len(raw) else header_idx
        data_idx = unit_idx + 1 if unit_idx + 1 < len(raw) else header_idx + 1
        headers = list(raw.iloc[header_idx].values)
        units = list(raw.iloc[unit_idx].values) if unit_idx != header_idx else [None] * len(headers)
        new_cols = []
        x_unit = None
        y_unit = None
        for h, u in zip(headers, units):
            h_s = str(h).strip()
            u_s = str(u).strip().lower() if u is not None else ""
            h_low = h_s.lower()
            name = h_s
            if h_low.startswith("удлинение") or h_low.startswith("деформация"):
                if "мм" in u_s or "mm" in u_s:
                    name = "Удлинение, мм"
                    x_unit = "мм"
                elif "%" in u_s:
                    name = "Удлинение, %"
                    x_unit = "%"
                else:
                    name = "Удлинение"
            elif h_low.startswith("стандартное"):
                if "мпа" in u_s or "mpa" in u_s:
                    name = "Напряжение, МПа"
                    y_unit = "мпа"
                elif "н" in u_s or "n" in u_s:
                    name = "Сила, Н"
                    y_unit = "н"
                else:
                    name = "Стандартное усилие"
            new_cols.append(name)
        df = raw.iloc[data_idx:].copy()
        df.columns = new_cols
        axis_pair = None
        if x_unit in {"мм", "%"} and y_unit in {"мпа", "н"}:
            axis_pair = (
                "Удлинение, мм" if x_unit == "мм" else "Удлинение, %",
                "Напряжение, МПа" if y_unit == "мпа" else "Сила, Н",
            )
        return df, axis_pair

    def _update_file_tools(self):
        self.file_delete_combo['values'] = sorted(self.files.keys())
        self.files_menu.delete(0, tk.END)
        for fname, meta in sorted(self.files.items()):
            label = f"📄 {fname} ({'XLS' if meta.get('ext') == '.xls' else 'XLSX'})"
            self.files_menu.add_checkbutton(label=label, onvalue=True, offvalue=False, variable=self.file_states[fname],
                                            command=self._on_file_filter_change)

    def _after_load(self):
        cols = set()
        for df in self.sheets_data.values():
            for c in df.columns:
                cols.add(str(c))
        self.columns = sorted(cols)
        self.x_select["values"] = self.columns
        self.y_select["values"] = self.columns
        if self.columns:
            x_candidates = [c for c in self.columns if
                            c.lower().startswith("удлинение") or c.lower().startswith("деформация")]
            y_candidates = [c for c in self.columns if
                            c.lower().startswith("напряжение") or c.lower().startswith("сила")]
            pref_pairs = [
                ("удлинение, мм", "напряжение, мпа"),
                ("удлинение, %", "напряжение, мпа"),
                ("удлинение, мм", "сила, н"),
                ("удлинение, %", "сила, н"),
            ]
            chosen_x = None
            chosen_y = None
            available_pairs = set()
            for pair in self.sample_axis_pairs.values():
                if pair:
                    available_pairs.add((pair[0].lower(), pair[1].lower()))
            for px, py in pref_pairs:
                x = next((c for c in x_candidates if c.lower() == px), None)
                y = next((c for c in y_candidates if c.lower() == py), None)
                if x and y and ((px, py) in available_pairs or not available_pairs):
                    chosen_x, chosen_y = x, y
                    break
            if not chosen_x:
                chosen_x = x_candidates[0] if x_candidates else self.columns[0]
            if not chosen_y:
                chosen_y = y_candidates[0] if y_candidates else (
                    self.columns[1] if len(self.columns) > 1 else self.columns[0])
            self.x_select.set(chosen_x)
            self.y_select.set(chosen_y)

        idx = 0
        for name in self._sorted_sample_names():
            if name not in self.sample_colors:
                self.sample_colors[name] = self._default_color(idx)
            if name not in self.sample_linewidths:
                self.sample_linewidths[name] = tk.StringVar(value="1.5")
            if name not in self.sample_linestyles:
                self.sample_linestyles[name] = tk.StringVar(value="-")
            if name not in self.sample_markers:
                self.sample_markers[name] = tk.StringVar(value="None")
            idx += 1

        self._update_file_tools()
        self._populate_samples_window()
        self._update_avg_styles_ui()
        self.plot_data()

    def _update_avg_styles_ui(self):
        if not hasattr(self, "avg_styles_container"):
            return
        for child in self.avg_styles_container.winfo_children():
            child.destroy()
        if not self.files:
            return

        ttk.Label(self.avg_styles_container, text="Стили средних:", font=("TkDefaultFont", 9, "bold")).grid(row=0,
                                                                                                            column=0,
                                                                                                            columnspan=4,
                                                                                                            sticky="w",
                                                                                                            pady=(5, 2))

        styles = ["-", "--", "-.", ":"]
        widths = ["1.0", "2.0", "3.0", "4.0", "5.0"]

        for i, fname in enumerate(sorted(self.files.keys()), 1):
            if fname not in self.file_avg_colors:
                self.file_avg_colors[fname] = self._default_color(i - 1)
            if fname not in self.file_avg_styles:
                self.file_avg_styles[fname] = tk.StringVar(value="--")
            if fname not in self.file_avg_widths:
                self.file_avg_widths[fname] = tk.StringVar(value="3.0")

            c_btn = tk.Canvas(self.avg_styles_container, width=12, height=12, bg=self.file_avg_colors[fname],
                              highlightthickness=1)
            c_btn.grid(row=i, column=0, padx=2)
            c_btn.bind("<Button-1>", lambda e, f=fname: self._choose_avg_color(f))

            lbl = ttk.Label(self.avg_styles_container, text=fname[:35] + "...", width=38)
            lbl.grid(row=i, column=1, padx=2, sticky="w")

            s_cb = ttk.Combobox(self.avg_styles_container, values=styles, textvariable=self.file_avg_styles[fname],
                                width=3, state="readonly")
            s_cb.grid(row=i, column=2, padx=2)
            s_cb.bind("<<ComboboxSelected>>", lambda e: self.plot_data())

            w_cb = ttk.Combobox(self.avg_styles_container, values=widths, textvariable=self.file_avg_widths[fname],
                                width=3, state="readonly")
            w_cb.grid(row=i, column=3, padx=2)
            w_cb.bind("<<ComboboxSelected>>", lambda e: self.plot_data())

    def _choose_avg_color(self, fname):
        color = colorchooser.askcolor(title=f"Цвет среднего для {fname}", initialcolor=self.file_avg_colors.get(fname))[
            1]
        if color:
            self.file_avg_colors[fname] = color
            self._update_avg_styles_ui()
            self.plot_data()

    def _populate_samples_window(self):
        parent = self.samples_container_frame
        for child in parent.winfo_children():
            child.destroy()

        self.sample_widgets = {}
        old_states = {n: v.get() for n, v in self.sample_states.items()}
        self.sample_states = {}

        styles = ["-", "--", "-.", ":", "None"]
        markers = ["None", "o", "s", "D", "v", "^", "<", ">", "p", "*", "+", "x"]
        widths = ["0.5", "1.0", "1.5", "2.0", "2.5", "3.0", "4.0", "5.0"]

        files_dict = {}
        sorted_names = self._sorted_sample_names()
        for name in sorted_names:
            fname = self.sample_file.get(name, "Unknown")
            if fname not in files_dict:
                files_dict[fname] = []
            files_dict[fname].append(name)

        row = 0
        for fname in sorted(files_dict.keys()):
            file_var = self.file_states.get(fname, tk.BooleanVar(value=True))

            def toggle_file(f=fname, v=file_var):
                state = v.get()
                for sname in files_dict[f]:
                    if sname in self.sample_states:
                        self.sample_states[sname].set(state)
                self.plot_data()

            file_frame = ttk.Frame(parent)
            file_frame.grid(row=row, column=0, columnspan=10, sticky="w", padx=5, pady=(5, 0))

            ttk.Checkbutton(file_frame, text=f"📁 {fname}", variable=file_var,
                            command=toggle_file, style="File.TCheckbutton").pack(side=tk.LEFT)

            ttk.Button(file_frame, text="Удалить файл",
                       command=lambda f=fname: self._delete_file_by_name(f)).pack(side=tk.LEFT, padx=10)

            row += 1

            for name in files_dict[fname]:
                val = old_states.get(name, True)
                var = tk.BooleanVar(value=val)
                self.sample_states[name] = var
                color = self.sample_colors.get(name) or self._default_color(0)

                sample_frame = ttk.Frame(parent)
                sample_frame.grid(row=row, column=0, columnspan=10, sticky="w", padx=(25, 5), pady=1)

                marker_canvas = tk.Canvas(sample_frame, width=12, height=12)
                marker_canvas.pack(side=tk.LEFT, padx=2)
                marker_canvas.create_rectangle(1, 1, 11, 11, fill=color, outline="black")

                chk = ttk.Checkbutton(sample_frame, text=name.replace(f"{fname}-", ""), variable=var,
                                      command=self.plot_data)
                chk.pack(side=tk.LEFT, padx=2)

                ttk.Button(sample_frame, text="🎨", width=3, command=lambda n=name: self._choose_color(n)).pack(
                    side=tk.LEFT, padx=2)

                ttk.Label(sample_frame, text="W:").pack(side=tk.LEFT, padx=2)
                w_cb = ttk.Combobox(sample_frame, values=widths, textvariable=self.sample_linewidths[name], width=4,
                                    state="readonly")
                w_cb.pack(side=tk.LEFT, padx=2)
                w_cb.bind("<<ComboboxSelected>>", lambda e: self.plot_data())

                ttk.Label(sample_frame, text="S:").pack(side=tk.LEFT, padx=2)
                s_cb = ttk.Combobox(sample_frame, values=styles, textvariable=self.sample_linestyles[name], width=5,
                                    state="readonly")
                s_cb.pack(side=tk.LEFT, padx=2)
                s_cb.bind("<<ComboboxSelected>>", lambda e: self.plot_data())

                ttk.Label(sample_frame, text="M:").pack(side=tk.LEFT, padx=2)
                m_cb = ttk.Combobox(sample_frame, values=markers, textvariable=self.sample_markers[name], width=5,
                                    state="readonly")
                m_cb.pack(side=tk.LEFT, padx=2)
                m_cb.bind("<<ComboboxSelected>>", lambda e: self.plot_data())

                ttk.Button(sample_frame, text="✕", width=3, command=lambda n=name: self._delete_sample(n)).pack(
                    side=tk.LEFT, padx=2)

                marker_canvas.bind("<Enter>", lambda e, n=name: self._show_widget_tooltip(e.widget, n))
                marker_canvas.bind("<Leave>", lambda e: self._hide_widget_tooltip())
                chk.bind("<Enter>", lambda e, n=name: self._show_widget_tooltip(e.widget, n))
                chk.bind("<Leave>", lambda e: self._hide_widget_tooltip())

                self.sample_widgets[name] = chk
                if not file_var.get():
                    chk.state(["disabled"])

                row += 1

    def _delete_file_by_name(self, fname):
        to_delete = [n for n, f in self.sample_file.items() if f == fname]
        for n in to_delete:
            for d in [self.sheets_data, self.sample_states, self.sample_colors, self.sample_widgets, self.sample_file]:
                if n in d: del d[n]
        if fname in self.files: del self.files[fname]
        if fname in self.file_states: del self.file_states[fname]
        self._after_load()

    def convert_to_newtons(self):
        self._convert_force_units(to_mpa=False)

    def convert_to_mpa(self):
        self._convert_force_units(to_mpa=True)

    def _convert_force_units(self, to_mpa=True):
        updated = False
        for name, df in self.sheets_data.items():
            fname = self.sample_file.get(name)
            if not fname: continue

            s0_list = self.file_S0.get(fname, [])
            order = self.file_samples_order.get(fname, [])
            if not s0_list or not order or name not in order: continue

            try:
                idx = order.index(name)
                s0 = float(s0_list[idx])
                if s0 <= 0: continue
            except (ValueError, TypeError):
                continue

            if to_mpa:
                col_n = self._get_col_by_tokens(df, ["сила", "н"]) or self._get_col_by_tokens(df, ["стандартное", "н"])
                if col_n:
                    df["Напряжение, МПа"] = pd.to_numeric(df[col_n], errors="coerce") / s0
                    updated = True
            else:
                col_mpa = self._get_col_by_tokens(df, ["напряжение", "мпа"]) or self._get_col_by_tokens(df,
                                                                                                        ["напряжение",
                                                                                                         "mpa"])
                if col_mpa:
                    df["Сила, Н"] = pd.to_numeric(df[col_mpa], errors="coerce") * s0
                    updated = True

        if updated:
            self._after_load()
            messagebox.showinfo("Готово", "Конвертация успешно завершена")
        else:
            messagebox.showwarning("Предупреждение", "Не найдены данные для конвертации или значения S0")

    def _default_color(self, idx):
        palette = ["#1f77b4", "#ff7f0e", "#2ca02c", "#d62728", "#9467bd", "#8c564b", "#e377c2", "#7f7f7f", "#bcbd22",
                   "#17becf"]
        return palette[idx % len(palette)]

    def _choose_color(self, name):
        color = colorchooser.askcolor(title="Выбор цвета", initialcolor=self.sample_colors.get(name))[1]
        if color:
            self.sample_colors[name] = color
            self.plot_data()
            self._populate_samples_window()

    def _reset_colors(self):
        i = 0
        for name in self.sheets_data.keys():
            self.sample_colors[name] = self._default_color(i)
            i += 1
        self.plot_data()
        self._populate_samples_window()

    def _on_file_filter_change(self):
        for name, chk in self.sample_widgets.items():
            file = self.sample_file.get(name)
            if file and not self.file_states.get(file, tk.BooleanVar(value=True)).get():
                chk.state(["disabled"])
            else:
                chk.state(["!disabled"])
        self.plot_data()

    def _delete_selected_file(self):
        fname = self.file_to_delete.get()
        if not fname:
            return
        self._delete_file_by_name(fname)

    def _delete_sample(self, name):
        if name in self.sheets_data: del self.sheets_data[name]
        if name in self.sample_states: del self.sample_states[name]
        if name in self.sample_colors: del self.sample_colors[name]
        if name in self.sample_widgets: del self.sample_widgets[name]
        fname = self.sample_file.get(name)
        if name in self.sample_file: del self.sample_file[name]
        if fname and fname in self.files:
            remaining = any(f == fname for f in self.sample_file.values())
            if not remaining:
                if fname in self.files: del self.files[fname]
                if fname in self.file_states: del self.file_states[fname]
        self._after_load()

    def _show_widget_tooltip(self, widget, name):
        fname = self.sample_file.get(name)
        if fname is None and "-" in name: fname = name.split("-", 1)[0]
        sample = name.split("-", 1)[1] if "-" in name else name
        text = f"{fname}-{sample}" if fname else name
        try:
            if self.tooltip and tk.Toplevel.winfo_exists(self.tooltip):
                self.tooltip.destroy()
        except Exception:
            self.tooltip = None
        tip = tk.Toplevel(self)
        tip.wm_overrideredirect(True)
        x = widget.winfo_rootx() + 20
        y = widget.winfo_rooty() + 10
        tip.geometry(f"+{x}+{y}")
        ttk.Label(tip, text=text, relief="solid").pack()
        self.tooltip = tip

    def _hide_widget_tooltip(self):
        if self.tooltip and tk.Toplevel.winfo_exists(self.tooltip):
            try:
                self.tooltip.destroy()
            finally:
                self.tooltip = None

    def _on_graph_hover(self, event):
        if event.inaxes != self.ax:
            if self.hover_annot.get_visible():
                self.hover_annot.set_visible(False)
                self.canvas.draw_idle()
            return
        for line in self.ax.lines:
            hit, _ = line.contains(event)
            if hit:
                name = line.get_label()
                fname = self.sample_file.get(name)
                sample = name.split("-", 1)[1] if "-" in name else name
                text = f"{fname}-{sample}" if fname else name
                self.hover_annot.xy = (event.xdata, event.ydata)
                self.hover_annot.set_text(text)
                self.hover_annot.set_visible(True)
                self.canvas.draw_idle()
                return
        if self.hover_annot.get_visible():
            self.hover_annot.set_visible(False)
            self.canvas.draw_idle()

    def _sorted_sample_names(self):
        names = list(self.sheets_data.keys())
        mode = self.sort_mode.get()
        reverse = self.sort_order.get() == "desc"
        if mode == "name":
            names.sort(reverse=reverse)
            return names
        y_col = self.y_select.get()
        if not y_col:
            names.sort(reverse=reverse)
            return names

        def score(n):
            df = self.sheets_data[n]
            if y_col in df.columns:
                try:
                    return pd.to_numeric(df[y_col], errors="coerce").max()
                except Exception:
                    return float("nan")
            return float("nan")

        names.sort(key=lambda n: (score(n), n), reverse=reverse)
        return names

    def apply_sort(self):
        self._populate_samples_window()
        self.plot_data()

    def reset_scale(self):
        self.xmin.set("0")
        self.xmax.set("")
        self.ymin.set("0")
        self.ymax.set("")
        self.plot_data()

    def plot_data(self):
        self.ax.clear()
        self.x_col = self.x_select.get()
        self.y_col = self.y_select.get()

        isavg = self.avg_on.get()
        try:
            salpha = float(self.sample_alpha.get()) if isavg else 1.0
            aalpha = float(self.avg_alpha.get())
        except Exception:
            salpha = 0.2 if isavg else 1.0
            aalpha = 0.9

        filecurves = {}
        for name in self._sorted_sample_names():
            if not self.sample_states.get(name, tk.BooleanVar(value=True)).get():
                continue
            fname = self.sample_file.get(name)
            if fname and not self.file_states.get(fname, tk.BooleanVar(value=True)).get():
                continue

            df = self.sheets_data.get(name)
            if df is None or self.x_col not in df.columns or self.y_col not in df.columns:
                continue

            x = pd.to_numeric(df[self.x_col], errors="coerce")
            y = pd.to_numeric(df[self.y_col], errors="coerce")
            validmask = x.notna() & y.notna()
            vx = x[validmask].values
            vy = y[validmask].values
            if vx.size <= 1:
                continue

            if fname not in filecurves:
                filecurves[fname] = []
            sidx = np.argsort(vx)
            filecurves[fname].append((vx[sidx], vy[sidx]))
            color = self.sample_colors.get(name, self._default_color(0))
            lw = float(self.sample_linewidths.get(name, tk.StringVar(value="1.5")).get())
            ls = self.sample_linestyles.get(name, tk.StringVar(value="-")).get()
            marker = self.sample_markers.get(name, tk.StringVar(value="None")).get()
            if marker == "None":
                marker = None
            if ls == "None":
                ls = ""

            label = name if not isavg else "_nolegend_"
            line = \
            self.ax.plot(vx, vy, label=label, color=color, linewidth=lw, linestyle=ls, marker=marker, markevery=0.1,
                         alpha=salpha)[0]
            try:
                line.set_picker(5)
            except Exception:
                pass

        if isavg:
            for fname, curves in filecurves.items():
                if not curves:
                    continue
                try:
                    maxxs = [c[0].max() for c in curves]
                    limitx = np.quantile(maxxs, 0.95)
                    xgrid = np.linspace(0, limitx, 500)
                    yinterpolated = []
                    for cx, cy in curves:
                        yi = np.interp(xgrid, cx, cy, left=0, right=np.nan)
                        yinterpolated.append(yi)
                    yavg = np.nanmean(yinterpolated, axis=0)
                    mask = ~np.isnan(yavg)
                    if not np.any(mask):
                        continue
                    color = self.file_avg_colors.get(fname, "black")
                    ls = self.file_avg_styles.get(fname, tk.StringVar(value="--")).get()
                    lw = float(self.file_avg_widths.get(fname, tk.StringVar(value="3.0")).get())
                    self.ax.plot(xgrid[mask], yavg[mask], color=color, linewidth=lw, linestyle=ls, label=f"avg-{fname}",
                                 alpha=aalpha)
                except Exception as e:
                    print(f"Error in average plot for {fname}: {e}")

        self.ax.grid(self.grid_on.get())

        axf = self._font_style_dict(self.font_ax_fam, self.font_ax_size, self.font_ax_color, self.font_ax_bold,
                                    self.font_ax_italic)
        tkf = self._font_style_dict(self.font_tick_fam, self.font_tick_size, self.font_tick_color, self.font_tick_bold,
                                    self.font_tick_italic)
        lgf = self._font_style_dict(self.font_leg_fam, self.font_leg_size, self.font_leg_color, self.font_leg_bold,
                                    self.font_leg_italic)

        self.ax.set_xlabel(self.x_col or "", fontdict=axf)
        self.ax.set_ylabel(self.y_col or "", fontdict=axf)

        for label in self.ax.get_xticklabels() + self.ax.get_yticklabels():
            label.set_fontfamily(tkf["family"])
            label.set_fontsize(tkf["size"])
            label.set_fontweight(tkf["weight"])
            label.set_fontstyle(tkf["style"])
            label.set_color(tkf["color"])

        if self.show_legend.get():
            legend = self.ax.legend()
            if legend:
                for text in legend.get_texts():
                    text.set_fontfamily(lgf["family"])
                    text.set_fontsize(lgf["size"])
                    text.set_fontweight(lgf["weight"])
                    text.set_fontstyle(lgf["style"])
                    text.set_color(lgf["color"])


        if self.scale_mode.get() == "log":
            self.ax.set_xscale("log")
            self.ax.set_yscale("log")
        else:
            self.ax.set_xscale("linear")
            self.ax.set_yscale("linear")

        try:
            xmin = float(self.xmin.get()) if self.xmin.get() else None
            xmax = float(self.xmax.get()) if self.xmax.get() else None
            ymin = float(self.ymin.get()) if self.ymin.get() else None
            ymax = float(self.ymax.get()) if self.ymax.get() else None
        except ValueError:
            xmin = xmax = ymin = ymax = None

        if any(v is not None for v in [xmin, xmax]):
            self.ax.set_xlim(left=xmin, right=xmax)
        if any(v is not None for v in [ymin, ymax]):
            self.ax.set_ylim(bottom=ymin, top=ymax)

        self.canvas.draw()

    def save_plot(self):
        path = filedialog.asksaveasfilename(defaultextension=".png", filetypes=(("PNG", "*.png"), ("PDF", "*.pdf")))
        if not path:
            return
        try:
            dpi = int(float(self.save_dpi.get())) if self.save_dpi.get() else 100
            w = float(self.save_w.get()) if self.save_w.get() else 6.0
            h = float(self.save_h.get()) if self.save_h.get() else 4.0
        except Exception:
            dpi, w, h = 100, 6.0, 4.0
        prev_size = self.fig.get_size_inches()
        self.fig.set_size_inches((w, h))
        try:
            self.fig.savefig(path, dpi=dpi, bbox_inches="tight")
        finally:
            self.fig.set_size_inches(prev_size)

    def save_session(self):
        path = filedialog.asksaveasfilename(defaultextension=".tvis",
                                            filetypes=(("Tensile Session", "*.tvis"), ("ZIP", "*.zip")))
        if not path:
            return
        state = {
            "x_col": self.x_select.get(),
            "y_col": self.y_select.get(),
            "scale_mode": self.scale_mode.get(),
            "grid_on": bool(self.grid_on.get()),
            "show_legend": bool(self.show_legend.get()),
            "xmin": self.xmin.get(),
            "xmax": self.xmax.get(),
            "ymin": self.ymin.get(),
            "ymax": self.ymax.get(),
            "sort_mode": self.sort_mode.get(),
            "sort_order": self.sort_order.get(),
            "avg_degree": self.avg_degree.get(),
            "avg_on": bool(self.avg_on.get()),
            "avg_alpha": self.avg_alpha.get(),
            "sample_alpha": self.sample_alpha.get(),

            "text_font": self.text_font.get(),
            "text_size": self.text_size.get(),
            "text_bold": bool(self.text_bold.get()),
            "text_italic": bool(self.text_italic.get()),
            "text_color": self.text_color.get(),

            "font_ax_fam": self.font_ax_fam.get(),
            "font_ax_size": self.font_ax_size.get(),
            "font_ax_color": self.font_ax_color.get(),
            "fontaxbold": bool(self.font_ax_bold.get()),
            "fontaxitalic": bool(self.font_ax_italic.get()),

            "fonttickfam": self.font_tick_fam.get(),
            "fontticksize": self.font_tick_size.get(),
            "fonttickcolor": self.font_tick_color.get(),
            "fonttickbold": bool(self.font_tick_bold.get()),
            "fonttickitalic": bool(self.font_tick_italic.get()),

            "fontlegfam": self.font_leg_fam.get(),
            "fontlegsize": self.font_leg_size.get(),
            "fontlegcolor": self.font_leg_color.get(),
            "fontlegbold": bool(self.font_leg_bold.get()),
            "fontlegitalic": bool(self.font_leg_italic.get()),

            "file_avg_colors": self.file_avg_colors,
            "file_avg_styles": {k: v.get() for k, v in self.file_avg_styles.items()},
            "file_avg_widths": {k: v.get() for k, v in self.file_avg_widths.items()},
            "sample_colors": self.sample_colors,
            "sample_linewidths": {k: v.get() for k, v in self.sample_linewidths.items()},
            "sample_linestyles": {k: v.get() for k, v in self.sample_linestyles.items()},
            "sample_markers": {k: v.get() for k, v in self.sample_markers.items()},
            "sample_file": self.sample_file,
            "sample_axis_pairs": self.sample_axis_pairs,
            "files": self.files,
            "file_S0": self.file_S0,
            "file_samples_order": self.file_samples_order,
            "sample_states_selected": [n for n, v in self.sample_states.items() if
                                       isinstance(v, tk.BooleanVar) and v.get()],
            "file_states_disabled": [n for n, v in self.file_states.items() if
                                     isinstance(v, tk.BooleanVar) and not v.get()],
        }
        try:
            with zipfile.ZipFile(path, "w", compression=zipfile.ZIP_DEFLATED) as zf:
                zf.writestr("state.json", json.dumps(state, ensure_ascii=False))
                for name, df in self.sheets_data.items():
                    b = io.StringIO()
                    df.to_csv(b, index=False)
                    zf.writestr(f"data/{name}.csv", b.getvalue())
        except Exception as e:
            messagebox.showerror("Ошибка", str(e))

    def load_session(self):
        path = filedialog.askopenfilename(filetypes=(("Tensile Session", "*.tvis"), ("ZIP", "*.zip")))
        if not path:
            return
        self._open_progress("Загрузка сессии", 1)

        def worker():
            try:
                with zipfile.ZipFile(path, "r") as zf:
                    state = json.loads(zf.read("state.json").decode("utf-8"))
                    names = [n for n in zf.namelist() if n.startswith("data/") and n.endswith(".csv")]
                    total = max(1, len(names))
                    self.after(0, lambda: self._set_progress_total(total))
                    data = {}
                    for i, name in enumerate(names, 1):
                        key = name.split("/", 1)[1][:-4]
                        txt = zf.read(name).decode("utf-8")
                        df = pd.read_csv(io.StringIO(txt))
                        data[key] = df
                        self.after(0, lambda i=i: self._update_progress(1, f"Загружено {i}/{total}"))

                def apply_state():
                    self.sheets_data = data
                    self.sample_colors = dict(state.get("sample_colors", {}))

                    self.sample_linewidths = {}
                    for k, v in state.get("sample_linewidths", {}).items():
                        self.sample_linewidths[k] = tk.StringVar(value=v)
                    self.sample_linestyles = {}
                    for k, v in state.get("sample_linestyles", {}).items():
                        self.sample_linestyles[k] = tk.StringVar(value=v)
                    self.sample_markers = {}
                    for k, v in state.get("sample_markers", {}).items():
                        self.sample_markers[k] = tk.StringVar(value=v)

                    self.sample_file = dict(state.get("sample_file", {}))
                    self.sample_axis_pairs = dict(state.get("sample_axis_pairs", {}))
                    self.files = dict(state.get("files", {}))
                    self.file_S0 = dict(state.get("file_S0", {}))
                    self.file_samples_order = dict(state.get("file_samples_order", {}))
                    self.file_states = {}
                    for fname in self.files.keys():
                        disabled = fname in set(state.get("file_states_disabled", []))
                        self.file_states[fname] = tk.BooleanVar(value=not disabled)
                    self.sample_states = {}
                    selected = set(state.get("sample_states_selected", []))
                    for name in self.sheets_data.keys():
                        self.sample_states[name] = tk.BooleanVar(value=(name in selected))

                    # Применяем текстовые стили
                    self.text_font.set(state.get("text_font", "sans-serif"))
                    self.text_size.set(state.get("text_size", 10))
                    self.text_bold.set(bool(state.get("text_bold", False)))
                    self.text_italic.set(bool(state.get("text_italic", False)))
                    self.text_color.set(state.get("text_color", "black"))

                    self.font_ax_fam.set(state.get("font_ax_fam", "Arial"))
                    self.font_ax_size.set(state.get("font_ax_size", "10"))
                    self.font_ax_color.set(state.get("font_ax_color", "black"))
                    self.font_ax_bold.set(state.get("fontaxbold", False))
                    self.font_ax_italic.set(state.get("fontaxitalic", False))

                    self.font_tick_fam.set(state.get("fonttickfam", "Arial"))
                    self.font_tick_size.set(state.get("fontticksize", "8"))
                    self.font_tick_color.set(state.get("fonttickcolor", "black"))
                    self.font_tick_bold.set(state.get("fonttickbold", False))
                    self.font_tick_italic.set(state.get("fonttickitalic", False))

                    self.font_leg_fam.set(state.get("fontlegfam", "Arial"))
                    self.font_leg_size.set(state.get("fontlegsize", "9"))
                    self.font_leg_color.set(state.get("fontlegcolor", "black"))
                    self.font_leg_bold.set(state.get("fontlegbold", False))
                    self.font_leg_italic.set(state.get("fontlegitalic", False))
                    self._after_load()

                    xc = state.get("x_col")
                    yc = state.get("y_col")
                    if xc and xc in self.columns: self.x_select.set(xc)
                    if yc and yc in self.columns: self.y_select.set(yc)

                    self.scale_mode.set(state.get("scale_mode", "linear"))
                    self.grid_on.set(bool(state.get("grid_on", True)))
                    self.show_legend.set(bool(state.get("show_legend", True)))
                    self.xmin.set(state.get("xmin", "0"))
                    self.xmax.set(state.get("xmax", ""))
                    self.ymin.set(state.get("ymin", "0"))
                    self.ymax.set(state.get("ymax", ""))
                    self.sort_mode.set(state.get("sort_mode", "name"))
                    self.sort_order.set(state.get("sort_order", "asc"))
                    self.avg_degree.set(state.get("avg_degree", 7))
                    self.avg_on.set(state.get("avg_on", False))
                    self.avg_alpha.set(state.get("avg_alpha", "0.9"))
                    self.sample_alpha.set(state.get("sample_alpha", "0.2"))

                    self.file_avg_colors = dict(state.get("file_avg_colors", {}))
                    self.file_avg_styles = {}
                    for k, v in state.get("file_avg_styles", {}).items():
                        self.file_avg_styles[k] = tk.StringVar(value=v)
                    self.file_avg_widths = {}
                    for k, v in state.get("file_avg_widths", {}).items():
                        self.file_avg_widths[k] = tk.StringVar(value=v)

                    self._close_progress()
                    self.plot_data()

                self.after(0, apply_state)
            except Exception as e:
                self.after(0, lambda: (self._close_progress(), messagebox.showerror("Ошибка", str(e))))

        threading.Thread(target=worker, daemon=True).start()

    def _open_progress(self, title, total):
        try:
            if getattr(self, "progress_win", None) and tk.Toplevel.winfo_exists(self.progress_win):
                self.progress_win.destroy()
        except Exception:
            pass
        win = tk.Toplevel(self)
        win.title(title)
        win.geometry("360x100")
        ttk.Label(win, text=title).pack(padx=10, pady=5)
        bar = ttk.Progressbar(win, maximum=total, mode="determinate")
        bar.pack(fill=tk.X, padx=10, pady=5)
        lbl = ttk.Label(win, text="")
        lbl.pack(padx=10, pady=5)
        self.progress_win = win
        self.progress_bar = bar
        self.progress_label = lbl
        self.progress_total = total
        self.progress_current = 0
        self._update_progress(0, "")

    def _set_progress_total(self, total):
        self.progress_total = total
        if getattr(self, "progress_bar", None):
            self.progress_bar.configure(maximum=total)

    def _update_progress(self, inc=1, text=None):
        self.progress_current = min(self.progress_total, self.progress_current + inc)
        if getattr(self, "progress_bar", None):
            self.progress_bar['value'] = self.progress_current
        if getattr(self, "progress_label", None) and text is not None:
            self.progress_label.configure(text=text)

    def _close_progress(self):
        try:
            if getattr(self, "progress_win", None) and tk.Toplevel.winfo_exists(self.progress_win):
                self.progress_win.destroy()
        finally:
            self.progress_win = None
            self.progress_bar = None
            self.progress_label = None

    def open_edit_data_window(self):
        if getattr(self, "edit_window", None) and tk.Toplevel.winfo_exists(self.edit_window):
            self.edit_window.lift()
            return
        win = tk.Toplevel(self)
        win.title("Изменить данные")
        win.geometry("380x260")
        self.edit_window = win
        ttk.Label(win, text="Файл").grid(row=0, column=0, padx=5, pady=5, sticky="w")
        self.edit_file = tk.StringVar()
        ttk.Combobox(win, state="readonly", values=sorted(self.files.keys()), textvariable=self.edit_file).grid(row=0,
                                                                                                                column=1,
                                                                                                                padx=5,
                                                                                                                pady=5,
                                                                                                                sticky="we")
        ttk.Label(win, text="Напряжение").grid(row=1, column=0, padx=5, pady=5, sticky="w")
        self.edit_y_type = tk.StringVar(value="МПа")
        ttk.Radiobutton(win, text="МПа", value="МПа", variable=self.edit_y_type).grid(row=1, column=1, padx=5, pady=5,
                                                                                      sticky="w")
        ttk.Radiobutton(win, text="Н", value="Н", variable=self.edit_y_type).grid(row=1, column=2, padx=5, pady=5,
                                                                                  sticky="w")
        ttk.Label(win, text="Удлинение").grid(row=2, column=0, padx=5, pady=5, sticky="w")
        self.edit_x_type = tk.StringVar(value="%")
        ttk.Radiobutton(win, text="%", value="%", variable=self.edit_x_type).grid(row=2, column=1, padx=5, pady=5,
                                                                                  sticky="w")
        ttk.Radiobutton(win, text="мм", value="мм", variable=self.edit_x_type).grid(row=2, column=2, padx=5, pady=5,
                                                                                    sticky="w")
        ttk.Label(win, text="Длина образца (мм)").grid(row=3, column=0, padx=5, pady=5, sticky="w")
        self.edit_length = tk.StringVar()
        ttk.Entry(win, textvariable=self.edit_length).grid(row=3, column=1, padx=5, pady=5, sticky="we")
        ttk.Button(win, text="Применить", command=self._apply_edit_data).grid(row=4, column=0, padx=5, pady=10,
                                                                              sticky="w")
        ttk.Button(win, text="Конвертировать", command=self._convert_data).grid(row=4, column=1, padx=5, pady=10,
                                                                                sticky="e")
        ttk.Button(win, text="Закрыть", command=win.destroy).grid(row=5, column=1, padx=5, pady=10, sticky="e")
        win.columnconfigure(1, weight=1)

    def _get_col_by_tokens(self, df, tokens):
        for c in df.columns:
            lc = str(c).lower()
            if all(t in lc for t in tokens):
                return c
        return None

    def _apply_edit_data(self):
        fname = self.edit_file.get()
        if not fname:
            return
        x_type = self.edit_x_type.get()
        y_type = self.edit_y_type.get()
        self._convert_data()
        self._refresh_after_data_change(x_type, y_type)

    def _convert_data(self):
        fname = self.edit_file.get()
        if not fname:
            return
        try:
            L = float(self.edit_length.get()) if self.edit_length.get() else None
        except Exception:
            L = None
        y_type = self.edit_y_type.get()
        s0_list = self.file_S0.get(fname, [])
        order = self.file_samples_order.get(fname, [])
        s0_by_sample = {sn: s0_list[i] for i, sn in enumerate(order)} if order and s0_list else {}
        for name, df in list(self.sheets_data.items()):
            if self.sample_file.get(name) != fname:
                continue
            col_pct = self._get_col_by_tokens(df, ["удлинение", "%"]) or self._get_col_by_tokens(df,
                                                                                                 ["удлинение,", "%"])
            col_mm_e = self._get_col_by_tokens(df, ["удлинение", "мм"]) or self._get_col_by_tokens(df,
                                                                                                   ["удлинение,", "мм"])
            col_mm_def = self._get_col_by_tokens(df, ["деформа", "мм"])
            col_mpa = self._get_col_by_tokens(df, ["напряжение", "мпа"]) or self._get_col_by_tokens(df, ["напряжение",
                                                                                                         "mpa"])
            col_n = self._get_col_by_tokens(df, ["сила", "н"])
            if L:
                if col_pct is None:
                    src = col_mm_e or col_mm_def
                    if src is not None:
                        s = pd.to_numeric(df[src], errors="coerce")
                        df["Удлинение, %"] = s / L * 100.0
                        col_pct = "Удлинение, %"
                if col_mm_e is None and col_mm_def is None and col_pct is not None:
                    s = pd.to_numeric(df[col_pct], errors="coerce")
                    df["Удлинение, мм"] = s * L / 100.0
                    df["Деформация, мм"] = df["Удлинение, мм"]
            if y_type == "МПа" and col_mpa is None and col_n is not None:
                s0 = s0_by_sample.get(name)
                if s0 is not None and s0 != 0:
                    force = pd.to_numeric(df[col_n], errors="coerce")
                    df["Напряжение, МПа"] = force / float(s0)
            self.sheets_data[name] = df
        self._refresh_after_data_change(self.edit_x_type.get(), self.edit_y_type.get())

    def _refresh_after_data_change(self, x_type, y_type):
        cols = set()
        for df in self.sheets_data.values():
            for c in df.columns:
                cols.add(str(c))
        self.columns = sorted(cols)
        self.x_select["values"] = self.columns
        self.y_select["values"] = self.columns
        if x_type == "%":
            x_name = next((c for c in self.columns if c.lower() == "удлинение, %"), None)
        else:
            x_name = next((c for c in self.columns if c.lower() == "удлинение, мм"), None)
        if y_type == "МПа":
            y_name = next((c for c in self.columns if c.lower() == "напряжение, мпа"), None)
        else:
            y_name = next((c for c in self.columns if c.lower() == "сила, н"), None)
        if x_name: self.x_select.set(x_name)
        if y_name: self.y_select.set(y_name)
        self._populate_samples_window()
        self.plot_data()


def main():
    app = TensileApp()
    app.mainloop()


if __name__ == "__main__":
    main()