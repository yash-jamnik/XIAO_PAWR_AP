"""
Serial Command Sender GUI (PyQt5)
---------------------------------
GUI version of the TIN -> MAC serial sender.

- Set port / baud / CSV / command prefix at the top, click Connect
- Type last digits of one or more TINs (e.g. "031 032 035") and press ENTER
- Commands are built at runtime as  prefix + mac_address  and sent one by one
  in a background thread (UI never freezes)
- Live log panel shows everything; the same log is saved to a timestamped file

Requirements:
    pip install pyserial pandas PyQt5

Run:
    python serial_gui.py
"""

import sys
import time
from datetime import datetime

try:
    import pandas as pd
except ImportError:
    print("pandas is not installed. Run:  pip install pandas")
    sys.exit(1)

try:
    import serial
    import serial.tools.list_ports
except ImportError:
    print("pyserial is not installed. Run:  pip install pyserial")
    sys.exit(1)

try:
    from PyQt5.QtCore import Qt, QThread, pyqtSignal
    from PyQt5.QtGui import QFont, QTextCursor
    from PyQt5.QtWidgets import (
        QApplication, QComboBox, QFileDialog, QGridLayout, QGroupBox,
        QHBoxLayout, QLabel, QLineEdit, QMainWindow, QPlainTextEdit,
        QPushButton, QVBoxLayout, QWidget,
    )
except ImportError:
    print("PyQt5 is not installed. Run:  pip install PyQt5")
    sys.exit(1)


# ---------------- CONFIG (defaults shown in the GUI, editable there) ----------------
DEFAULT_PORT = "COM18"
DEFAULT_BAUD = "1000000" #"460800" #"115200"
DEFAULT_CSV = "batch_mac.csv"
# Command buttons shown in the GUI.  needs_target=True -> asks for a target MAC
# and builds:  prefix + csv_mac + "," + target_mac
COMMANDS = {
    "LED":    {"prefix": "[+]led,",    "needs_target": False, "raw": False},
    "TEL":    {"prefix": "[+]tel,",    "needs_target": False, "raw": False},
    "SPLASH": {"prefix": "[+]splash,", "needs_target": False, "raw": False},
    "CLEAR":  {"prefix": "[+]clear,",  "needs_target": False, "raw": False},
    "JOIN":   {"prefix": "[+]join,",   "needs_target": True,  "raw": False},
    "PING":   {"prefix": "[+]ping_all",   "needs_target": False, "raw": True},
    "LIST":   {"prefix": "[+]list,0,20",   "needs_target": False, "raw": True},
}

DEFAULT_COMMAND = "LED"
TIN_COLUMN = "TIN Number"
MAC_COLUMN = "mac address"
LINE_ENDING = "\r\n"
READ_TIMEOUT = 2.0
DELAY_BETWEEN_COMMANDS = 5.0
RESULT_PREFIX = "[+]res,"      # device lines starting with this are "wanted" results
_PREFIX = "[+]dev,"

# -------------------------------------------------------------------------------------
TEL_RESPONSE_TIMEOUT = 12.0   # near the other config constants at the top
ACK_WAIT_TIMEOUT = 10.0          # <-- ADD here

class SerialWorker(QThread):
    """Owns the serial port and processes TIN batches in the background."""

    log = pyqtSignal(str, str)          # (level, message) -> shown in GUI + file
    result = pyqtSignal(str)            # raw "[+]res,..." line -> Results panel
    connected = pyqtSignal(bool)        # True on connect, False on disconnect/fail

    def __init__(self):
        super().__init__()
        self.ser = None
        self.df = None
        self._queue = []                # list of (digits, prefix, target_mac_or_None)
        self._running = True
        self._connect_params = None     # (port, baud) when a connect is requested
        self._disconnect_requested = False
        self._last_res_mac = None          # <-- ADD: MAC from the latest [+]res line
        self._pending_echo = None          # <-- ADD: command we expect to see echoed back
        self._seen_plus_lines = set()      # <-- ADD: dedup set for "[+]" result lines
        self._pending_ack = None         # <-- goes here
        self._ack_received = False       # <-- goes here
        self._ack_prefix = False         # <-- also add this (needed for the TEL prefix-match fix)
        self._current_tin = None          # <-- ADD: TIN associated with the in-flight command
    # ---------- called from the GUI thread ----------
    def request_connect(self, port, baud):
        self._connect_params = (port, baud)

    def request_disconnect(self):
        self._disconnect_requested = True

    def enqueue(self, digits_list, prefix, target_mac=None, raw=False):
        if raw:
            self._queue.append((None, prefix, None, True))
            return
        for d in digits_list:
            self._queue.append((d, prefix, target_mac, False))

    def set_sheet(self, df):
        self.df = df

    def stop(self):
        self._running = False

    # ---------- worker thread ----------
    def run(self):
        while self._running:
            if self._connect_params:
                port, baud = self._connect_params
                self._connect_params = None
                self._do_connect(port, baud)

            if self._disconnect_requested:
                self._disconnect_requested = False
                self._do_disconnect()

            self._read_incoming()

            if self._queue and self.ser and self.ser.is_open:
                digits, prefix, target_mac, raw = self._queue.pop(0)
                self._process_one(digits, prefix, target_mac, raw)
                # _send() now blocks until ack-or-timeout internally —
                # no more DELAY_BETWEEN_COMMANDS sleep needed here
            else:
                time.sleep(0.05)

        self._do_disconnect(silent=True)

    def _do_connect(self, port, baud):
        self._do_disconnect(silent=True)
        try:
            self.ser = serial.Serial(
                port=port, baudrate=int(baud),
                bytesize=serial.EIGHTBITS, parity=serial.PARITY_NONE,
                stopbits=serial.STOPBITS_ONE, timeout=READ_TIMEOUT,
            )
            time.sleep(2)  # let the device settle (some boards reset on connect)
            self.ser.reset_input_buffer()
            self.ser.reset_output_buffer()
            self.log.emit("INFO", f"Connected to {port} @ {baud} baud")
            self.connected.emit(True)
        except (serial.SerialException, ValueError) as e:
            self.ser = None
            self.log.emit("ERROR", f"Could not open {port}: {e}")
            self.connected.emit(False)

    def _do_disconnect(self, silent=False):
        if self.ser:
            try:
                self.ser.close()
            except Exception:
                pass
            self.ser = None
            if not silent:
                self.log.emit("INFO", "Port closed.")
                self.connected.emit(False)

    def _find_mac(self, last_digits):
        matches = self.df[self.df[TIN_COLUMN].str.endswith(last_digits, na=False)]
        if matches.empty:
            return None, f"No TIN found ending with '{last_digits}'"
        if len(matches) > 1:
            tins = ", ".join(matches[TIN_COLUMN].tolist())
            return None, f"Multiple TINs match '{last_digits}': {tins}. Be more specific."
        row = matches.iloc[0]
        mac = row[MAC_COLUMN]
        if pd.isna(mac) or not str(mac).strip():
            return None, f"TIN {row[TIN_COLUMN]} found, but its MAC cell is empty."
        return (row[TIN_COLUMN], str(mac).strip()), None

    def _process_one(self, digits, prefix, target_mac=None, raw=False):
        if raw:
            self.log.emit("INFO", f"Sending raw command (no TIN/MAC lookup)")
            self._send(prefix, tin=None)
            return

        if self.df is None:
            self.log.emit("ERROR", "No CSV sheet loaded.")
            return
        self.log.emit("INFO", f"Looking up TIN ending '{digits}'")
        result, error = self._find_mac(digits)
        if error:
            self.log.emit("ERROR", error)
            self.result.emit(f"[+]failed,{digits},lookup_error:{error}")   # <-- ADD
            return
        tin, mac = result
        command = prefix + mac
        if target_mac:
            command += "," + target_mac
        self.log.emit("INFO", f"Matched TIN: {tin}  MAC: {mac}")
        self._send(command, tin=tin)

    def _send(self, command, tin=None):
        try:
            self.log.emit("SENT", command)
            self._pending_echo = command
            self._pending_ack = command
            self._ack_received = False
            self._current_tin = tin
            self.ser.write((command + LINE_ENDING).encode("utf-8"))
            self.ser.flush()

            deadline = time.time() + ACK_WAIT_TIMEOUT
            while time.time() < deadline:
                self._read_incoming()
                if self._ack_received:
                    self.log.emit("INFO", f"Ack received for: {command}")
                    break
                time.sleep(0.02)
            else:
                self.log.emit("WARN", f"(no ack within {ACK_WAIT_TIMEOUT}s) — moving on")
                if tin:
                    self.result.emit(f"[+]failed,{tin},{command}")

            self._pending_ack = None
            self._current_tin = None
        except serial.SerialException as e:
            self.log.emit("ERROR", f"Serial error: {e}")
            self._do_disconnect()

    def _read_incoming(self):
        if not (self.ser and self.ser.is_open):
            return False
        received = False
        try:
            while self.ser.in_waiting:
                line = self.ser.readline()
                if not line:
                    break
                decoded = line.decode("utf-8", errors="replace").strip()
                if not decoded:
                    continue

                if self._pending_echo is not None and decoded == self._pending_echo:
                    self._pending_echo = None
                    continue

                received = True
                self.log.emit("RECV", decoded)

                if decoded.startswith("[+]") or decoded.startswith("[+]res,"):
                    if decoded not in self._seen_plus_lines:
                        self._seen_plus_lines.add(decoded)
                        self.result.emit(decoded)

                    if decoded.startswith(RESULT_PREFIX):
                        parts = decoded[len(RESULT_PREFIX):].split(",")
                        if parts:
                            self._last_res_mac = parts[0].strip().upper()

                    if self._pending_ack is not None:
                        check = decoded[len(RESULT_PREFIX):] if decoded.startswith(RESULT_PREFIX) else decoded
                        if check.startswith(self._pending_ack):
                            self._ack_received = True

        except (serial.SerialException, OSError) as e:
            self.log.emit("ERROR", f"Serial read error: {e}")
            self._do_disconnect()
        return received

    def clear_results_memory(self):
            """Called when the user clears the Results panel — forget everything
            seen so far so old lines can't 'block' fresh duplicates later, and
            so the clear is a true reset."""
            self._seen_plus_lines.clear()

class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()

        self.setWindowTitle("Serial TIN Command Sender")
        self.resize(1000, 560)

        self.log_filename = datetime.now().strftime("serial_log_%Y%m%d_%H%M%S.txt")
        self.log_file = open(self.log_filename, "a", encoding="utf-8")
        self.results_filename = datetime.now().strftime("results_%Y%m%d_%H%M%S.txt")
        self.results_file = open(self.results_filename, "a", encoding="utf-8")
        self.df = None
        self._result_line_no = 0          # <-- ADD: running counter for result numbering

        self.worker = SerialWorker()
        self.worker.log.connect(self.append_log)
        self.worker.result.connect(self.append_result)
        self.worker.connected.connect(self.on_connected_changed)
        self.worker.start()

        self._build_ui()
        self.append_log("INFO", "Initialising the code!!!")
        self.append_log("INFO", f"Logs are being saved to: {self.log_filename}")

    def clear_results_panel(self):
        """Clears the Results view AND permanently wipes the results file
        + dedup memory + numbering, so cleared entries never come back."""
        self.result_view.clear()
        self._result_line_no = 0
        self.worker.clear_results_memory()

        # Truncate the results file on disk so it's gone for good
        try:
            self.results_file.close()
        except Exception:
            pass
        self.results_file = open(self.results_filename, "w", encoding="utf-8")  # 'w' truncates

    # ---------------- UI ----------------
    def _build_ui(self):
        central = QWidget()
        root = QVBoxLayout(central)

        # --- Connection settings ---
        conn_box = QGroupBox("Connection")
        grid = QGridLayout(conn_box)

        grid.addWidget(QLabel("Port:"), 0, 0)
        self.port_combo = QComboBox()
        self.port_combo.setEditable(True)
        self.refresh_ports()
        self.port_combo.setCurrentText(DEFAULT_PORT)
        grid.addWidget(self.port_combo, 0, 1)

        self.refresh_btn = QPushButton("Refresh")
        self.refresh_btn.clicked.connect(self.refresh_ports)
        grid.addWidget(self.refresh_btn, 0, 2)

        grid.addWidget(QLabel("Baud:"), 0, 3)
        self.baud_combo = QComboBox()
        self.baud_combo.setEditable(True)
        self.baud_combo.addItems(["9600", "19200", "38400", "57600", "115200"])
        self.baud_combo.setCurrentText(DEFAULT_BAUD)
        grid.addWidget(self.baud_combo, 0, 4)

        self.connect_btn = QPushButton("Connect")
        self.connect_btn.clicked.connect(self.toggle_connect)
        grid.addWidget(self.connect_btn, 0, 5)

        grid.addWidget(QLabel("CSV sheet:"), 1, 0)
        self.csv_edit = QLineEdit(DEFAULT_CSV)
        grid.addWidget(self.csv_edit, 1, 1, 1, 3)
        self.browse_btn = QPushButton("Browse…")
        self.browse_btn.clicked.connect(self.browse_csv)
        grid.addWidget(self.browse_btn, 1, 4)
        self.load_btn = QPushButton("Load CSV")
        self.load_btn.clicked.connect(self.load_csv)
        grid.addWidget(self.load_btn, 1, 5)

        root.addWidget(conn_box)

        # --- Command selection buttons ---
        from PyQt5.QtWidgets import QButtonGroup
        cmd_box = QGroupBox("Command")
        ch = QHBoxLayout(cmd_box)

        # Create the target MAC widgets FIRST, so they exist before any
        # button's toggled signal fires on_command_changed.
        self.target_label = QLabel("Target MAC:")
        self.target_edit = QLineEdit()
        self.target_edit.setPlaceholderText("e.g. AA:BB:CC:DD:EE:FF")
        # Pressing Enter in the target MAC field jumps to the TIN box
        self.target_edit.returnPressed.connect(lambda: self.tin_edit.setFocus())
        self.target_label.setVisible(False)
        self.target_edit.setVisible(False)

        self.cmd_group = QButtonGroup(self)
        self.cmd_group.setExclusive(True)
        self.cmd_buttons = {}
        for name, spec in COMMANDS.items():
            btn = QPushButton(name)
            btn.setCheckable(True)
            # Never steal keyboard focus — typing/Enter keeps going to the TIN box
            btn.setFocusPolicy(Qt.NoFocus)
            btn.setToolTip(f"Sends: {spec['prefix']}<mac from CSV>"
                           + (",<target MAC>" if spec["needs_target"] else ""))
            self.cmd_group.addButton(btn)
            self.cmd_buttons[name] = btn
            ch.addWidget(btn)
            btn.toggled.connect(self.on_command_changed)
        self.cmd_buttons[DEFAULT_COMMAND].setChecked(True)

        ch.addWidget(self.target_label)
        ch.addWidget(self.target_edit, stretch=1)

        root.addWidget(cmd_box)

        # --- TIN input ---
        input_box = QGroupBox("Send")
        h = QHBoxLayout(input_box)
        h.addWidget(QLabel("TIN last digits:"))
        self.tin_edit = QLineEdit()
        self.tin_edit.setPlaceholderText("e.g. 031  or  031 032 035  — press Enter to send")
        self.tin_edit.returnPressed.connect(self.on_enter)   # <-- ENTER sends
        self.tin_edit.setEnabled(False)
        h.addWidget(self.tin_edit, stretch=1)
        self.send_btn = QPushButton("Send")
        self.send_btn.setFocusPolicy(Qt.NoFocus)
        self.send_btn.clicked.connect(self.on_enter)
        self.send_btn.setEnabled(False)
        h.addWidget(self.send_btn)
        root.addWidget(input_box)

        # --- Two log panels: All Logs (observation) + Results (wanted) ---
        from PyQt5.QtWidgets import QSplitter
        splitter = QSplitter(Qt.Horizontal)

        # Left: everything, raw
        log_box = QGroupBox(f"All Logs  (saved to {self.log_filename})")
        v = QVBoxLayout(log_box)
        self.log_view = QPlainTextEdit()
        self.log_view.setReadOnly(True)
        self.log_view.setFont(QFont("Consolas", 10))
        self.log_view.setMaximumBlockCount(5000)  # keep GUI snappy on long runs
        v.addWidget(self.log_view)
        self.clear_btn = QPushButton("Clear")
        self.clear_btn.clicked.connect(self.log_view.clear)
        v.addWidget(self.clear_btn, alignment=Qt.AlignRight)
        splitter.addWidget(log_box)

        # Right: only [+]res result lines, parsed
        res_box = QGroupBox(f"Results  (saved to {self.results_filename})")
        rv = QVBoxLayout(res_box)
        self.result_view = QPlainTextEdit()
        self.result_view.setReadOnly(True)
        self.result_view.setFont(QFont("Consolas", 10))
        self.result_view.setMaximumBlockCount(5000)
        rv.addWidget(self.result_view)
        self.clear_res_btn = QPushButton("Clear")
        self.clear_res_btn.clicked.connect(self.clear_results_panel)
        rv.addWidget(self.clear_res_btn, alignment=Qt.AlignRight)
        splitter.addWidget(res_box)

        splitter.setSizes([380, 380])
        root.addWidget(splitter, stretch=1)

        self.setCentralWidget(central)
        self.tin_edit.setFocus()

    # ---------------- actions ----------------
    def refresh_ports(self):
        current = self.port_combo.currentText()
        self.port_combo.clear()
        ports = [p.device for p in serial.tools.list_ports.comports()]
        self.port_combo.addItems(ports if ports else [])
        if current:
            self.port_combo.setCurrentText(current)

    def browse_csv(self):
        path, _ = QFileDialog.getOpenFileName(self, "Select CSV sheet", "", "CSV files (*.csv);;All files (*)")
        if path:
            self.csv_edit.setText(path)
            self.load_csv()

    def load_csv(self):
        path = self.csv_edit.text().strip()
        try:
            df = pd.read_csv(path, dtype=str)
        except FileNotFoundError:
            self.append_log("ERROR", f"CSV file not found: {path}")
            return
        except Exception as e:
            self.append_log("ERROR", f"Could not read CSV: {e}")
            return

        df.columns = df.columns.str.strip()
        missing = [c for c in (TIN_COLUMN, MAC_COLUMN) if c not in df.columns]
        if missing:
            self.append_log("ERROR", f"Missing column(s) in CSV: {missing}")
            self.append_log("ERROR", f"Found columns: {list(df.columns)}")
            return

        df[TIN_COLUMN] = df[TIN_COLUMN].str.strip()
        df[MAC_COLUMN] = df[MAC_COLUMN].str.strip()
        self.df = df
        self.worker.set_sheet(df)
        self.append_log("INFO", f"Loaded {len(df)} row(s) from {path}")

    def toggle_connect(self):
        if self.connect_btn.text() == "Connect":
            if self.df is None:
                self.load_csv()  # try auto-loading the CSV from the path field
            port = self.port_combo.currentText().strip()
            baud = self.baud_combo.currentText().strip()
            self.append_log("INFO", f"Connecting to {port} @ {baud}…")
            self.connect_btn.setEnabled(False)
            self.worker.request_connect(port, baud)
        else:
            self.worker.request_disconnect()

    def on_connected_changed(self, is_connected):
        self.connect_btn.setEnabled(True)
        self.connect_btn.setText("Disconnect" if is_connected else "Connect")
        self.tin_edit.setEnabled(is_connected)
        self.send_btn.setEnabled(is_connected)
        if is_connected:
            self.tin_edit.setFocus()

    def selected_command(self):
        for name, btn in self.cmd_buttons.items():
            if btn.isChecked():
                return name
        return DEFAULT_COMMAND

    def on_command_changed(self):
        needs_target = COMMANDS[self.selected_command()]["needs_target"]
        self.target_label.setVisible(needs_target)
        self.target_edit.setVisible(needs_target)

        # Put the cursor where the user will type next.
        # (guard with hasattr: this fires once during __init__ before tin_edit exists)
        if hasattr(self, "tin_edit"):
            if needs_target and not self.target_edit.text().strip():
                self.target_edit.setFocus()
            elif self.tin_edit.isEnabled():
                self.tin_edit.setFocus()

    def on_enter(self):
        cmd_name = self.selected_command()
        spec = COMMANDS[cmd_name]
        prefix = spec["prefix"]

        if spec.get("raw"):
            self.append_log("INFO", f"--- {cmd_name}: sending raw command ---")
            self.worker.enqueue([], prefix, raw=True)
            self.tin_edit.clear()
            return

        text = self.tin_edit.text().strip()
        if not text:
            return
        parts = [p for p in text.replace(",", " ").split() if p]
        valid = [p for p in parts if p.isdigit()]
        invalid = [p for p in parts if not p.isdigit()]
        if invalid:
            self.append_log("WARN", f"Ignoring non-digit input: {invalid}")
        if not valid:
            return

        target_mac = None
        if spec["needs_target"]:
            target_mac = self.target_edit.text().strip().upper()
            import re
            if not re.fullmatch(r"([0-9A-F]{2}:){5}[0-9A-F]{2}", target_mac):
                self.append_log("ERROR",
                                f"{cmd_name} needs a valid target MAC (AA:BB:CC:DD:EE:FF). "
                                f"Got: '{target_mac or '(empty)'}'")
                self.target_edit.setFocus()
                return

        batch_info = f"--- {cmd_name}: batch of {len(valid)} TIN(s): {', '.join(valid)}"
        if target_mac:
            batch_info += f"  target: {target_mac}"
        self.append_log("INFO", batch_info + " ---")

        self.worker.enqueue(valid, prefix, target_mac)
        self.tin_edit.clear()

    # ---------------- logging ----------------
    def append_log(self, level, message):
        timestamp = datetime.now().strftime("%H:%M:%S")
        tag = {"SENT": ">>>", "RECV": "<<<"}.get(level, level)
        line = f"[{timestamp}] {tag:5s} {message}"
        self.log_view.appendPlainText(line)
        self.log_view.moveCursor(QTextCursor.End)

        # Mirror everything to the terminal screen as well
        print(line, flush=True)

        full = f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}  {level:5s}  {message}\n"
        self.log_file.write(full)
        self.log_file.flush()

    def append_result(self, raw_line):
        """Any line starting with '[+]' is shown in the Results panel,
        numbered sequentially. '[+]res,...' lines get pretty-parsed;
        everything else is shown raw.

        Expected [+]res format:
            [+]res,<MAC>,<TIN>,<val1>,<fw_version>,<val2>,<rssi>
        """
        timestamp = datetime.now().strftime("%H:%M:%S")

        if raw_line.startswith(RESULT_PREFIX):
            payload = raw_line[len(RESULT_PREFIX):]
            parts = [p.strip() for p in payload.split(",")]
            if len(parts) >= 6:
                mac, tin, val1, fw, val2, rssi = parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]
                body = (f"TIN: {tin} | MAC: {mac} | "
                        f"val1: {val1} | FW: {fw} | val2: {val2} | RSSI: {rssi}")
            else:
                body = f"RAW: {raw_line}"
        elif raw_line.startswith("[+]failed,"):
            payload = raw_line[len("[+]failed,"):]
            parts = payload.split(",", 1)
            tin = parts[0] if parts else "?"
            cmd = parts[1] if len(parts) > 1 else ""
            body = f"FAILED — TIN: {tin}  (no ack for: {cmd})"
        else:
            body = raw_line

        self._result_line_no += 1
        pretty = f"{self._result_line_no}. [{timestamp}] {body}"

        self.result_view.appendPlainText(pretty)
        self.result_view.moveCursor(QTextCursor.End)

        print(f"[RESULT] {pretty}", flush=True)

        self.results_file.write(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}  {raw_line}\n")
        self.results_file.flush()

    def closeEvent(self, event):
        self.worker.stop()
        self.worker.wait(2000)
        self.append_log("INFO", "Application closed.")
        self.log_file.close()
        self.results_file.close()
        event.accept()


def main():
    app = QApplication(sys.argv)
    window = MainWindow()
    window.show()
    sys.exit(app.exec_())


if __name__ == "__main__":
    main()