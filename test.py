"""
ESL Command Sender - PyQt5 GUI

- Enter device numbers (the short suffix) e.g.  1, 5, 31-330, 210
  These get expanded/decoded into full TINs like: EN0010000001, EN0010000005, ... EN0010000210
- Pick a command (Show Splash Screen / Clear Display) or send an image update
- Commands are sent one by one in a background thread so the UI never freezes
- Live log of each response is shown in the window

Run with:  python esl_command_gui.py
Requires:  pip install PyQt5 requests
"""

import sys
import os
import requests
from PyQt5.QtWidgets import (
    QApplication, QWidget, QVBoxLayout, QHBoxLayout, QLabel, QTextEdit,
    QPushButton, QComboBox, QLineEdit, QFileDialog, QSpinBox, QMessageBox
)
from PyQt5.QtCore import QThread, pyqtSignal, Qt


class EnterToSendTextEdit(QTextEdit):
    """QTextEdit that emits enter_pressed when Enter is hit (without Shift).
    Shift+Enter still inserts a normal newline, in case you want to paste
    a multi-line list instead of a comma-separated one."""
    enter_pressed = pyqtSignal()

    def keyPressEvent(self, event):
        if event.key() in (Qt.Key_Return, Qt.Key_Enter):
            if event.modifiers() & Qt.ShiftModifier:
                super().keyPressEvent(event)
            else:
                self.enter_pressed.emit()
        else:
            super().keyPressEvent(event)


# ----------------------------- Config / API -----------------------------

BASE_URL = "https://tgx-device-api.sit.intellobots.com"
HEADERS_BASE = {
    "X-API-Key": "dVpqVHBkNFBuSjMzMkljSVpnSEc4b3hRTlptM0FHMndybzdEWmdCaWNRUXlQSm5hQXpTdnppRE1UUTEwQzZCSg="
}

# TIN prefix: EN001 + 7 digits, e.g. EN0010000210 -> prefix "EN001", 7-digit suffix "0000210"
TIN_PREFIX = "EN001"
TIN_SUFFIX_LEN = 7

# Used for image updates when the user doesn't pick a specific file
DEFAULT_IMAGE_PATH = "images/anwaliya.png"

COMMANDS = {
    "Show Splash Screen": {
        "update_id": "INTERNAL_TEST",
        "data": {
            "message_type": "ESL_COMMAND",
            "device_action": "SHOW_SPLASH_SCREEN"
        }
    },
    "Clear Display": {
        "update_id": "INTERNAL_TEST",
        "data": {
            "message_type": "ESL_COMMAND",
            "device_action": "CLEAR_DISPLAY"
        }
    },
}


def number_to_tin(n: int) -> str:
    """Convert a short number (e.g. 1, 210, 330) into a full device TIN."""
    return f"{TIN_PREFIX}{n:0{TIN_SUFFIX_LEN}d}"


def parse_number_list(text: str):
    """
    Parse a string like "1, 5, 31-330, 210" into a sorted list of unique ints.
    Supports comma-separated single numbers and ranges (a-b).
    """
    numbers = set()
    parts = [p.strip() for p in text.replace("\n", ",").split(",") if p.strip()]
    for part in parts:
        if "-" in part:
            start_str, end_str = part.split("-", 1)
            start, end = int(start_str.strip()), int(end_str.strip())
            if start > end:
                start, end = end, start
            numbers.update(range(start, end + 1))
        else:
            numbers.add(int(part))
    return sorted(numbers)


def execute_esl_command(device_tin, payload):
    payload = dict(payload)
    payload["device_tin"] = device_tin
    headers = HEADERS_BASE.copy()
    headers["Content-Type"] = "application/json"
    url = f"{BASE_URL}/tgx-data-writer"
    return requests.post(url, json=payload, headers=headers, timeout=15)


def execute_esl_image_update(device_tin, filepath):
    with open(filepath, "rb") as f:
        files = {"file": f}
        data = {"device_tin": device_tin}
        headers = HEADERS_BASE.copy()
        url = f"{BASE_URL}/esl-image-update"
        return requests.post(url, files=files, data=data, headers=headers, timeout=30)


# ----------------------------- Worker Thread -----------------------------

class CommandWorker(QThread):
    log_signal = pyqtSignal(str)
    finished_signal = pyqtSignal()

    def __init__(self, device_numbers, command_name, image_path, delay_seconds):
        super().__init__()
        self.device_numbers = device_numbers
        self.command_name = command_name
        self.image_path = image_path
        self.delay_seconds = delay_seconds
        self._stop_requested = False

    def stop(self):
        self._stop_requested = True

    def run(self):
        total = len(self.device_numbers)
        for idx, num in enumerate(self.device_numbers, start=1):
            if self._stop_requested:
                self.log_signal.emit("Stopped by user.")
                break

            tin = number_to_tin(num)
            try:
                if self.command_name == "__IMAGE__":
                    response = execute_esl_image_update(tin, self.image_path)
                else:
                    payload = COMMANDS[self.command_name]
                    response = execute_esl_command(tin, payload)
                self.log_signal.emit(
                    f"[{idx}/{total}] {tin} -> {response.status_code}: {response.text}"
                )
            except Exception as e:
                self.log_signal.emit(f"[{idx}/{total}] {tin} -> ERROR: {e}")

            if self.delay_seconds > 0 and idx < total:
                self.msleep(int(self.delay_seconds * 1000))

        self.finished_signal.emit()


# ----------------------------- Main Window -----------------------------

class ESLGui(QWidget):
    def __init__(self):
        super().__init__()
        self.worker = None
        self.image_path = None
        self.init_ui()

    def init_ui(self):
        self.setWindowTitle("ESL Command Sender")
        self.resize(650, 550)

        layout = QVBoxLayout()

        # Device number input
        layout.addWidget(QLabel(
            "Enter device numbers (comma separated, ranges allowed):\n"
            "e.g.  1, 5, 210, 31-330  ->  decoded as EN0010000001, EN0010000005, EN0010000210, ..."
        ))
        self.device_input = EnterToSendTextEdit()
        self.device_input.setPlaceholderText("e.g. 1, 5, 31-330  (press Enter to send, Shift+Enter for newline)")
        self.device_input.setFixedHeight(80)
        self.device_input.enter_pressed.connect(self.send_commands)
        layout.addWidget(self.device_input)

        # Preview button
        preview_row = QHBoxLayout()
        self.preview_btn = QPushButton("Preview Decoded TINs")
        self.preview_btn.clicked.connect(self.preview_tins)
        preview_row.addWidget(self.preview_btn)
        self.count_label = QLabel("Devices: 0")
        preview_row.addWidget(self.count_label)
        preview_row.addStretch()
        layout.addLayout(preview_row)

        # Command selection
        cmd_row = QHBoxLayout()
        cmd_row.addWidget(QLabel("Command:"))
        self.command_combo = QComboBox()
        self.command_combo.addItems(list(COMMANDS.keys()) + ["Send Image (esl-image-update)"])
        self.command_combo.currentTextChanged.connect(self.on_command_changed)
        cmd_row.addWidget(self.command_combo)
        layout.addLayout(cmd_row)

        # Image picker (hidden unless "Send Image" selected)
        self.image_row = QHBoxLayout()
        self.image_path_edit = QLineEdit()
        self.image_path_edit.setPlaceholderText(f"Leave empty to use default: {DEFAULT_IMAGE_PATH}")
        self.image_browse_btn = QPushButton("Browse...")
        self.image_browse_btn.clicked.connect(self.browse_image)
        self.image_row.addWidget(self.image_path_edit)
        self.image_row.addWidget(self.image_browse_btn)
        layout.addLayout(self.image_row)

        # Sequential Start/End range (image mode) - alternative to typing numbers above
        self.range_row = QHBoxLayout()
        self.range_row.addWidget(QLabel("Sequential range:"))
        self.range_row.addWidget(QLabel("Start:"))
        self.start_spin = QSpinBox()
        self.start_spin.setRange(1, 9999999)
        self.start_spin.setValue(31)
        self.range_row.addWidget(self.start_spin)
        self.range_row.addWidget(QLabel("End:"))
        self.end_spin = QSpinBox()
        self.end_spin.setRange(1, 9999999)
        self.end_spin.setValue(50)
        self.range_row.addWidget(self.end_spin)
        self.use_range_btn = QPushButton("Use This Range")
        self.use_range_btn.clicked.connect(self.apply_range_to_input)
        self.range_row.addWidget(self.use_range_btn)
        self.range_row.addStretch()
        layout.addLayout(self.range_row)

        self.set_image_row_visible(False)

        # Delay setting
        delay_row = QHBoxLayout()
        delay_row.addWidget(QLabel("Delay between requests (seconds):"))
        self.delay_spin = QSpinBox()
        self.delay_spin.setRange(0, 60)
        self.delay_spin.setValue(1)
        delay_row.addWidget(self.delay_spin)
        delay_row.addStretch()
        layout.addLayout(delay_row)

        # Send / Stop buttons
        btn_row = QHBoxLayout()
        self.send_btn = QPushButton("Send Commands")
        self.send_btn.clicked.connect(self.send_commands)
        self.stop_btn = QPushButton("Stop")
        self.stop_btn.clicked.connect(self.stop_commands)
        self.stop_btn.setEnabled(False)
        btn_row.addWidget(self.send_btn)
        btn_row.addWidget(self.stop_btn)
        layout.addLayout(btn_row)

        # Log output
        layout.addWidget(QLabel("Log:"))
        self.log_output = QTextEdit()
        self.log_output.setReadOnly(True)
        layout.addWidget(self.log_output)

        clear_log_btn = QPushButton("Clear Log")
        clear_log_btn.clicked.connect(self.log_output.clear)
        layout.addWidget(clear_log_btn)

        self.setLayout(layout)

    def set_image_row_visible(self, visible):
        self.image_path_edit.setVisible(visible)
        self.image_browse_btn.setVisible(visible)
        for i in range(self.range_row.count()):
            widget = self.range_row.itemAt(i).widget()
            if widget:
                widget.setVisible(visible)

    def on_command_changed(self, text):
        self.set_image_row_visible(text == "Send Image (esl-image-update)")

    def browse_image(self):
        path, _ = QFileDialog.getOpenFileName(self, "Select Image", "", "Images (*.png *.jpg *.jpeg *.bmp)")
        if path:
            self.image_path_edit.setText(path)

    def apply_range_to_input(self):
        start, end = self.start_spin.value(), self.end_spin.value()
        if start > end:
            start, end = end, start
        self.device_input.setPlainText(f"{start}-{end}")
        self.preview_tins()

    def get_device_numbers(self):
        text = self.device_input.toPlainText().strip()
        if not text:
            return []
        try:
            return parse_number_list(text)
        except ValueError:
            QMessageBox.warning(self, "Invalid input", "Please enter valid numbers/ranges, e.g. 1, 5, 31-330")
            return None

    def preview_tins(self):
        numbers = self.get_device_numbers()
        if numbers is None:
            return
        if not numbers:
            self.count_label.setText("Devices: 0")
            self.log_output.append("No devices entered.")
            return
        self.count_label.setText(f"Devices: {len(numbers)}")
        preview = ", ".join(number_to_tin(n) for n in numbers[:10])
        more = f" ... (+{len(numbers) - 10} more)" if len(numbers) > 10 else ""
        self.log_output.append(f"Preview: {preview}{more}")

    def send_commands(self):
        if self.worker is not None and self.worker.isRunning():
            return  # a send is already in progress, ignore extra Enter presses

        numbers = self.get_device_numbers()
        if numbers is None:
            return
        if not numbers:
            QMessageBox.warning(self, "No devices", "Please enter at least one device number.")
            return

        command_name = self.command_combo.currentText()
        image_path = None

        if command_name == "Send Image (esl-image-update)":
            image_path = self.image_path_edit.text().strip() or DEFAULT_IMAGE_PATH
            if not os.path.isfile(image_path):
                QMessageBox.warning(self, "Image not found", f"Could not find image file:\n{image_path}")
                return
            command_name = "__IMAGE__"

        self.count_label.setText(f"Devices: {len(numbers)}")
        self.log_output.append(f"--- Sending '{self.command_combo.currentText()}' to {len(numbers)} device(s) ---")

        self.send_btn.setEnabled(False)
        self.stop_btn.setEnabled(True)

        self.worker = CommandWorker(
            device_numbers=numbers,
            command_name=command_name,
            image_path=image_path,
            delay_seconds=self.delay_spin.value(),
        )
        self.worker.log_signal.connect(self.append_log)
        self.worker.finished_signal.connect(self.on_finished)
        self.worker.start()

    def stop_commands(self):
        if self.worker:
            self.worker.stop()

    def append_log(self, text):
        self.log_output.append(text)
        self.log_output.verticalScrollBar().setValue(self.log_output.verticalScrollBar().maximum())

    def on_finished(self):
        self.log_output.append("--- Done ---")
        self.send_btn.setEnabled(True)
        self.stop_btn.setEnabled(False)


if __name__ == "__main__":
    app = QApplication(sys.argv)
    gui = ESLGui()
    gui.show()
    sys.exit(app.exec_())