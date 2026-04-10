import os
import sys
import shutil
import subprocess

def build():
    cwd = os.path.abspath(os.path.dirname(__file__))
    build_dir = os.path.join(cwd, "build")
    dist_dir = os.path.join(cwd, "dist")
    spec_file = os.path.join(cwd, "TensileVisualizer.spec")
    if os.path.isdir(build_dir):
        shutil.rmtree(build_dir)
    if os.path.isdir(dist_dir):
        shutil.rmtree(dist_dir)
    if os.path.isfile(spec_file):
        os.remove(spec_file)
    cmd = [
        sys.executable,
        "-m",
        "PyInstaller",
        "--noconfirm",
        "--onefile",
        "--windowed",
        "--name",
        "TensileVisualizer",
        "--icon",
        os.path.join(cwd, "pics", "ico.ico"),
        "app.py",
    ]
    r = subprocess.run(cmd, cwd=cwd)
    if r.returncode != 0:
        raise SystemExit(r.returncode)
    exe_path = os.path.join(dist_dir, "TensileVisualizer.exe")
    print(exe_path)

if __name__ == "__main__":
    build()