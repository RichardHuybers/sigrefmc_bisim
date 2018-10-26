#!/usr/bin/env python
import os
import random
import sh
import sys


def strip_ext(files, ext):
    return [f[:-len(ext)] for f in filter(lambda f: f.endswith(ext), files)]


def generate_all(files=None):
    if files is None:
        files = list(filter(os.path.isfile, os.listdir(os.curdir)))

    files = strip_ext(list(set(files)), ".lps")
    random.shuffle(files)

    for m in files:

        # for every file ending with .lps

        lps_file = m+".lps"
        ldd_file = m+".ldd"
        bdd_file = m+".bdd"

        # if the LDD file does not exist, generate it

        if not os.path.isfile(ldd_file):
            print("Generating {}...".format(ldd_file))
            try:
                sh.lps2lts_sym("-rf", "--order=par-prev", "--when", "--vset=lddmc", "--sylvan-sizes=25,28,25,28", lps_file, ldd_file, _err=sys.stdout, _out=sys.stdout, _out_bufsize=1)
                # sh.lps2lts_sym("-rf", "--order=chain", "--saturation=sat-like", "--sat-granularity=10", "--save-sat-levels", "--when", "--vset=lddmc", "--sylvan-sizes=30,30,28,28", lps_file, ldd_file, _err=sys.stdout, _out=sys.stdout, _out_bufsize=1)
            except sh.ErrorReturnCode:
                print("Error")
        if not os.path.isfile(ldd_file):
            print("File {} could not be generated!".format(ldd_file))
            continue

        # if the BDD files does not exist, generate it

        if not os.path.isfile(bdd_file):
            print("Generating {}...".format(bdd_file))
            sh.ldd2bdd(ldd_file, bdd_file, "--sylvan-sizes=25,28,25,28")
        if not os.path.isfile(bdd_file):
            print("File {} could not be generated!".format(bdd_file))
            continue


if __name__ == "__main__":
    if len(sys.argv) > 1:
        generate_all(sys.argv[1:])
    else:
        generate_all()
