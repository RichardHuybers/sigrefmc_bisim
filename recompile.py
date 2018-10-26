#!/usr/bin/env python
from contextlib import contextmanager
import os
from sh import cmake, make, mv
import sys


@contextmanager
def cd(newdir):
    prevdir = os.getcwd()
    os.chdir(os.path.expanduser(newdir))
    try:
        yield
    finally:
        os.chdir(prevdir)


if __name__ == "__main__":
    # git clone
    with cd("tool"):
        print(cmake('.', _out=sys.stdout))
        print(make(_out=sys.stdout))
        mv("src/sigrefmc", "..")
        mv("src/sigrefmc_ht", "..")
