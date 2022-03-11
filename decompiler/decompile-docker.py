#!/usr/bin/env python3

# Copyright (c) 2022, Kry10 Limited
# SPDX-License-Identifier: BSD-2-Clause

import subprocess
import sys

from pathlib import Path

# The actual functionality is in decompile.py, so we don't
# have to duplicate argument parsing here.
decompile = Path(__file__).resolve().parent / 'decompile.py'
subprocess.run([decompile, '--docker'] + sys.argv[1:], check=True)
