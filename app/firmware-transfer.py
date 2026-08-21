"""
Firmware Finder & Uploader
---------------------------
1. Point it at a build output folder (source path).
2. It locates: merged.hex, zephyr.signed.bin, zephyr.signed.hex
   inside that folder (recursively).
3. Copies each into a local "image" folder using a naming pattern you define.
4. Three buttons let you send each file individually to the gateway over SFTP:
      [ Send signed.bin ]  [ Send signed.hex ]  [ Send merged.hex ]

Install:
    pip install PyQt5 paramiko

Run:
    python3 scp_uploader.py
"""

import sys
import os
import shutil
import traceback
from datetime import datetime

from PyQt5.QtWidgets import (
    QApplication, QWidget, QLabel, QLineEdit, QPushButton,
    QFileDialog, QVBoxLayout, QHBoxLayout, QGridLayout,
    QMessageBox, QTextEdit, QGroupBox
)
from PyQt5.QtCore import QThread, pyqtSignal

import paramiko


# ---- Target filenames we search for inside the source folder ----
TARGET_FILES = {
    "signed_bin": "zephyr.signed.bin",
    "signed_hex": "zephyr.signed.hex",
    "merged_hex": "merged.hex",
}

DEFAULT_LOCAL_IMAGE_DIR = os.path.join(os.getcwd(), "app/image")
# Pattern tokens available: {basename} {ext} {date} {time}
DEFAULT_NAME_PATTERN = "{basename}_{date}{ext}"

DEFAULT_HOST = "gw0003000006"
DEFAULT_PORT = 22
DEFAULT_REMOTE_DIR = "ble_firmwares"  # base folder removed as requested; fully editable now


class UploadWorker(QThread):
    finished_ok = pyqtSignal(str)
    finished_err = pyqtSignal(str)
    progress = pyqtSignal(str)

    def __init__(self, host, port, username, password, local_path, remote_path):
        super().__init__()
        self.host = host
        self.port = port
        self.username = username
        self.password = password
        self.local_path = local_path
        self.remote_path = remote_path

    def run(self):
        try:
            self.progress.emit(f"Connecting to {self.username}@{self.host}:{self.port} ...")
            ssh = paramiko.SSHClient()
            ssh.set_missing_host_key_policy(paramiko.AutoAddPolicy())
            ssh.connect(hostname=self.host, port=self.port,
                        username=self.username, password=self.password, timeout=15)

            sftp = ssh.open_sftp()
            remote_dir = os.path.dirname(self.remote_path).replace("\\", "/")
            self._mkdir_p(sftp, remote_dir)

            self.progress.emit(f"Uploading:\n  {self.local_path}\n  -> {self.remote_path}")

            def cb(sent, total):
                pct = (sent / total) * 100 if total else 0
                self.progress.emit(f"  ... {pct:5.1f}%  ({sent}/{total} bytes)")

            sftp.put(self.local_path, self.remote_path, callback=cb)
            sftp.close()
            ssh.close()
            self.finished_ok.emit(f"Upload complete:\n{self.remote_path}")
        except Exception as e:
            self.finished_err.emit(f"{e}\n\n{traceback.format_exc()}")

    @staticmethod
    def _mkdir_p(sftp, remote_dir):
        if not remote_dir:
            return
        dirs = []
        d = remote_dir
        while d and d != "/":
            dirs.append(d)
            d = os.path.dirname(d).replace("\\", "/")
        for d in reversed(dirs):
            try:
                sftp.stat(d)
            except IOError:
                try:
                    sftp.mkdir(d)
                except IOError:
                    pass


class UploaderUI(QWidget):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Firmware Finder & Uploader")
        self.setMinimumWidth(680)
        self.worker = None
        # local paths of the copied files, filled in after "Locate & Prepare"
        self.local_files = {"signed_bin": None, "signed_hex": None, "merged_hex": None}
        self._build_ui()

    def _build_ui(self):
        main_layout = QVBoxLayout()

        # ---- Source folder ----
        src_group = QGroupBox("Source Build Folder")
        src_layout = QHBoxLayout()
        self.source_path_edit = QLineEdit()
        self.source_path_edit.setPlaceholderText("Folder containing the build output...")
        src_browse_btn = QPushButton("Browse...")
        src_browse_btn.clicked.connect(self.browse_source_folder)
        src_layout.addWidget(self.source_path_edit)
        src_layout.addWidget(src_browse_btn)
        src_group.setLayout(src_layout)
        main_layout.addWidget(src_group)

        # ---- Local storage (image folder) + naming pattern ----
        local_group = QGroupBox("Local Storage (image folder)")
        local_layout = QGridLayout()

        local_layout.addWidget(QLabel("Image folder:"), 0, 0)
        self.image_dir_edit = QLineEdit(DEFAULT_LOCAL_IMAGE_DIR)
        img_browse_btn = QPushButton("Browse...")
        img_browse_btn.clicked.connect(self.browse_image_folder)
        local_layout.addWidget(self.image_dir_edit, 0, 1)
        local_layout.addWidget(img_browse_btn, 0, 2)

        local_layout.addWidget(QLabel("Naming (part1_part2_part3):"), 1, 0)

        name_parts_layout = QHBoxLayout()
        self.name_part1_edit = QLineEdit("pap")
        self.name_part1_edit.setPlaceholderText("e.g. pap")
        self.name_part2_edit = QLineEdit(datetime.now().strftime("%d%m%y"))
        self.name_part2_edit.setPlaceholderText("e.g. date")
        self.name_part3_edit = QLineEdit("")
        self.name_part3_edit.setPlaceholderText("e.g. convention/note")

        name_parts_layout.addWidget(self.name_part1_edit)
        name_parts_layout.addWidget(QLabel("_"))
        name_parts_layout.addWidget(self.name_part2_edit)
        name_parts_layout.addWidget(QLabel("_"))
        name_parts_layout.addWidget(self.name_part3_edit)

        local_layout.addLayout(name_parts_layout, 1, 1, 1, 2)

        pattern_hint = QLabel(
            "Final name = part1_part2_part3_<originalname><ext>  "
            "(e.g. pap_260820_esl_zephyr.signed.bin)"
        )
        pattern_hint.setStyleSheet("color:#666; font-style: italic;")
        local_layout.addWidget(pattern_hint, 2, 0, 1, 3)

        locate_btn = QPushButton("Locate && Prepare Files")
        locate_btn.clicked.connect(self.locate_and_prepare)
        local_layout.addWidget(locate_btn, 3, 0, 1, 3)

        local_group.setLayout(local_layout)
        main_layout.addWidget(local_group)

        # ---- Found files preview ----
        self.found_label = QLabel("No files located yet.")
        self.found_label.setStyleSheet("color:#333;")
        self.found_label.setWordWrap(True)
        main_layout.addWidget(self.found_label)

        # ---- Gateway connection ----
        conn_group = QGroupBox("Gateway Connection")
        conn_layout = QGridLayout()

        conn_layout.addWidget(QLabel("Host / IP:"), 0, 0)
        self.host_edit = QLineEdit(DEFAULT_HOST)
        conn_layout.addWidget(self.host_edit, 0, 1)

        conn_layout.addWidget(QLabel("Port:"), 0, 2)
        self.port_edit = QLineEdit(str(DEFAULT_PORT))
        self.port_edit.setFixedWidth(60)
        conn_layout.addWidget(self.port_edit, 0, 3)

        conn_layout.addWidget(QLabel("Gateway User ID:"), 1, 0)
        self.username_edit = QLineEdit()
        self.username_edit.setPlaceholderText("e.g. intello")
        conn_layout.addWidget(self.username_edit, 1, 1)

        conn_layout.addWidget(QLabel("Password:"), 1, 2)
        self.password_edit = QLineEdit()
        self.password_edit.setEchoMode(QLineEdit.Password)
        conn_layout.addWidget(self.password_edit, 1, 3)

        conn_layout.addWidget(QLabel("Remote folder:"), 2, 0)
        self.remote_dir_edit = QLineEdit(DEFAULT_REMOTE_DIR)
        self.remote_dir_edit.setPlaceholderText("e.g. ble_firmwares  or  /home/intello/ble_firmwares")
        conn_layout.addWidget(self.remote_dir_edit, 2, 1, 1, 3)

        conn_group.setLayout(conn_layout)
        main_layout.addWidget(conn_group)

        # ---- Three send buttons ----
        btn_group = QGroupBox("Send to Gateway")
        btn_layout = QHBoxLayout()

        self.btn_send_signed_bin = QPushButton("1. Send signed.bin")
        self.btn_send_signed_bin.clicked.connect(lambda: self.send_file("signed_bin"))
        self.btn_send_signed_hex = QPushButton("2. Send signed.hex")
        self.btn_send_signed_hex.clicked.connect(lambda: self.send_file("signed_hex"))
        self.btn_send_merged_hex = QPushButton("3. Send merged.hex")
        self.btn_send_merged_hex.clicked.connect(lambda: self.send_file("merged_hex"))

        for b in (self.btn_send_signed_bin, self.btn_send_signed_hex, self.btn_send_merged_hex):
            b.setEnabled(False)
            btn_layout.addWidget(b)

        btn_group.setLayout(btn_layout)
        main_layout.addWidget(btn_group)

        # ---- Log ----
        log_group = QGroupBox("Log")
        log_layout = QVBoxLayout()
        self.log_box = QTextEdit()
        self.log_box.setReadOnly(True)
        log_layout.addWidget(self.log_box)
        log_group.setLayout(log_layout)
        main_layout.addWidget(log_group)

        self.setLayout(main_layout)

    # ---------------- helpers ----------------

    def log(self, text):
        self.log_box.append(text)

    def browse_source_folder(self):
        path = QFileDialog.getExistingDirectory(self, "Select build output folder")
        if path:
            self.source_path_edit.setText(path)

    def browse_image_folder(self):
        path = QFileDialog.getExistingDirectory(self, "Select local image folder")
        if path:
            self.image_dir_edit.setText(path)

    def find_file(self, root, filename):
        """Recursively search root for an exact filename match, return first hit."""
        for dirpath, _dirs, files in os.walk(root):
            if filename in files:
                return os.path.join(dirpath, filename)
        return None

    def apply_pattern(self, original_path):
        base = os.path.basename(original_path)
        name, ext = os.path.splitext(base)

        # handle double extensions like zephyr.signed.bin -> name keeps "zephyr.signed"
        # (splitext only strips the last one, which is what we want here)

        part1 = self.name_part1_edit.text().strip()
        part2 = self.name_part2_edit.text().strip()
        part3 = self.name_part3_edit.text().strip()

        pieces = [p for p in (part1, part2, part3, name) if p]
        new_name = "_".join(pieces) + ext
        return new_name

    def locate_and_prepare(self):
        source = self.source_path_edit.text().strip()
        if not source or not os.path.isdir(source):
            QMessageBox.warning(self, "Invalid folder", "Please select a valid source folder.")
            return

        image_dir = self.image_dir_edit.text().strip()
        if not image_dir:
            QMessageBox.warning(self, "Missing image folder", "Please set a local image folder.")
            return
        os.makedirs(image_dir, exist_ok=True)

        # ---- Clear out old files already sitting in the image folder ----
        self.log(f"\n--- Clearing old files in: {image_dir} ---")
        removed_count = 0
        for entry in os.listdir(image_dir):
            entry_path = os.path.join(image_dir, entry)
            try:
                if os.path.isfile(entry_path) or os.path.islink(entry_path):
                    os.remove(entry_path)
                    removed_count += 1
                elif os.path.isdir(entry_path):
                    shutil.rmtree(entry_path)
                    removed_count += 1
            except Exception as e:
                self.log(f"  WARNING: could not remove {entry_path}: {e}")
        self.log(f"  Removed {removed_count} old item(s).")

        self.log(f"\n--- Locating files under: {source} ---")

        found_summary = []
        any_missing = False

        for key, filename in TARGET_FILES.items():
            found_path = self.find_file(source, filename)
            if not found_path:
                self.log(f"  NOT FOUND: {filename}")
                found_summary.append(f"{filename}: NOT FOUND")
                self.local_files[key] = None
                any_missing = True
                continue

            new_name = self.apply_pattern(found_path)
            dest_path = os.path.join(image_dir, new_name)
            try:
                shutil.copy2(found_path, dest_path)
                self.local_files[key] = dest_path
                self.log(f"  Found: {found_path}\n    -> copied to: {dest_path}")
                found_summary.append(f"{filename} -> {new_name}")
            except Exception as e:
                self.log(f"  ERROR copying {found_path}: {e}")
                self.local_files[key] = None
                any_missing = True

        self.found_label.setText("\n".join(found_summary))

        # enable buttons only for files successfully located
        self.btn_send_signed_bin.setEnabled(self.local_files["signed_bin"] is not None)
        self.btn_send_signed_hex.setEnabled(self.local_files["signed_hex"] is not None)
        self.btn_send_merged_hex.setEnabled(self.local_files["merged_hex"] is not None)

        if any_missing:
            QMessageBox.warning(
                self, "Some files missing",
                "One or more target files were not found. Check the log for details."
            )
        else:
            QMessageBox.information(self, "Ready", "All three files located and prepared.")

    def build_remote_path(self, local_path):
        remote_dir = self.remote_dir_edit.text().strip().rstrip("/")
        filename = os.path.basename(local_path)
        if remote_dir:
            return f"{remote_dir}/{filename}"
        return filename

    def send_file(self, key):
        local_path = self.local_files.get(key)
        if not local_path or not os.path.isfile(local_path):
            QMessageBox.warning(self, "File not ready",
                                 "Run 'Locate & Prepare Files' first.")
            return

        host = self.host_edit.text().strip()
        try:
            port = int(self.port_edit.text().strip())
        except ValueError:
            QMessageBox.warning(self, "Invalid port", "Port must be a number.")
            return

        username = self.username_edit.text().strip()
        password = self.password_edit.text()

        if not host or not username:
            QMessageBox.warning(self, "Missing info", "Gateway user ID and host are required.")
            return

        remote_path = self.build_remote_path(local_path)

        self.log(f"\n--- Sending {TARGET_FILES[key]} ---")
        self.log(f"Local:  {local_path}")
        self.log(f"Remote: {username}@{host}:{port} -> {remote_path}")

        self._set_buttons_enabled(False)

        self.worker = UploadWorker(host, port, username, password, local_path, remote_path)
        self.worker.progress.connect(self.log)
        self.worker.finished_ok.connect(self.on_success)
        self.worker.finished_err.connect(self.on_error)
        self.worker.start()

    def _set_buttons_enabled(self, enabled):
        self.btn_send_signed_bin.setEnabled(enabled and self.local_files["signed_bin"] is not None)
        self.btn_send_signed_hex.setEnabled(enabled and self.local_files["signed_hex"] is not None)
        self.btn_send_merged_hex.setEnabled(enabled and self.local_files["merged_hex"] is not None)

    def on_success(self, msg):
        self.log(msg)
        self._set_buttons_enabled(True)
        QMessageBox.information(self, "Success", msg)

    def on_error(self, msg):
        self.log(f"ERROR:\n{msg}")
        self._set_buttons_enabled(True)
        QMessageBox.critical(self, "Upload failed", msg.split("\n\n")[0])


def main():
    app = QApplication(sys.argv)
    ui = UploaderUI()
    ui.show()
    sys.exit(app.exec_())


if __name__ == "__main__":
    main()