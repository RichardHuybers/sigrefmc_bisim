#!/usr/bin/env python
from itertools import product
import fileinput
import os
import sh
import sys


BOLD = '\033[1;37m'
NORMAL = '\033[0m'


def gen_abp(data, version):
    target = "abp_{data}-{version}.mcrl2".format(**locals())

    # generate mCRL2 file

    if not os.path.isfile(target):
        print(BOLD + "Generating {target}...".format(**locals()) + NORMAL)
        sources = 'data{data}.mcrl2 abp.mcrl2 abp-{version}.mcrl2'.format(**locals()).split()
        with open(target, 'w') as out:
            out.writelines(fileinput.input(sources))

    # generate LPS

    lps_target = "abp_{data}-{version}.lps".format(**locals())

    if not os.path.isfile(lps_target):
        print(BOLD + "Generating {lps_target}...".format(**locals()) + NORMAL)
        sh.mcrl22lps("-Dfvn", target, lps_target, _err=sys.stdout)


def gen_onebit(data, version):
    target = "onebit_{data}-{version}.mcrl2".format(**locals())

    # generate mCRL2 file

    if not os.path.isfile(target):
        print(BOLD + "Generating {target}...".format(**locals()) + NORMAL)
        sources = 'data{data}.mcrl2 onebit.mcrl2 onebit-{version}.mcrl2'.format(**locals()).split()
        with open(target, 'w') as out:
            out.writelines(fileinput.input(sources))

    # generate LPS

    lps_target = "onebit_{data}-{version}.lps".format(**locals())

    if not os.path.isfile(lps_target):
        print(BOLD + "Generating {lps_target}...".format(**locals()) + NORMAL)
        sh.mcrl22lps("-Dfvn", target, lps_target, _err=sys.stdout)


def gen_brp(data, llen, retries, version):
    target = "brp_{data}_{llen}_{retries}-{version}.mcrl2".format(**locals())

    # generate mCRL2 file

    if not os.path.isfile(target):
        print(BOLD + "Generating {target}...".format(**locals()) + NORMAL)
        sources = 'data{data}.mcrl2 l{llen}.mcrl2 n{retries}.mcrl2 brp.mcrl2 brp-{version}.mcrl2'.format(**locals()).split()
        with open(target, 'w') as out:
            out.writelines(fileinput.input(sources))

    # generate LPS

    lps_target = "brp_{data}_{llen}_{retries}-{version}.lps".format(**locals())

    if not os.path.isfile(lps_target):
        print(BOLD + "Generating {lps_target}...".format(**locals()) + NORMAL)
        sh.mcrl22lps("-Dfvn", target, lps_target, _err=sys.stdout)


def gen_swp(data, window, version):
    target = "swp_{data}_{window}-{version}.mcrl2".format(**locals())

    # generate mCRL2 file

    if not os.path.isfile(target):
        print(BOLD + "Generating {target}...".format(**locals()) + NORMAL)
        sources = 'data{data}.mcrl2 n{window}.mcrl2 swp.mcrl2 swp-{version}.mcrl2'.format(**locals()).split()
        with open(target, 'w') as out:
            out.writelines(fileinput.input(sources))

    # generate LPS

    lps_target = "swp_{data}_{window}-{version}.lps".format(**locals())

    if not os.path.isfile(lps_target):
        print(BOLD + "Generating {lps_target}...".format(**locals()) + NORMAL)
        sh.mcrl22lps("-Dfvn", target, lps_target, _err=sys.stdout)


def gen_dkr(ring, version):
    target = "dkr_{ring}-{version}.mcrl2".format(**locals())

    # generate mCRL2 file

    if not os.path.isfile(target):
        print(BOLD + "Generating {target}...".format(**locals()) + NORMAL)
        sources = 'n{ring}.mcrl2 triple_channel.mcrl2 dkr.mcrl2 leader{ring}.mcrl2 leader-{version}.mcrl2'.format(**locals()).split()
        with open(target, 'w') as out:
            out.writelines(fileinput.input(sources))

    # generate LPS

    lps_target = "dkr_{ring}-{version}.lps".format(**locals())

    if not os.path.isfile(lps_target):
        print(BOLD + "Generating {lps_target}...".format(**locals()) + NORMAL)
        sh.mcrl22lps("-Dfvn", target, lps_target, _err=sys.stdout)


def gen_franklin(ring, l, version):
    target = "franklin_{ring}_{l}-{version}.mcrl2".format(**locals())

    # generate mCRL2 file

    if not os.path.isfile(target):
        print(BOLD + "Generating {target}...".format(**locals()) + NORMAL)
        sources = 'n{ring}.mcrl2 l{l}.mcrl2 triple_channel.mcrl2 franklin.mcrl2 leader{ring}.mcrl2 leader-{version}.mcrl2'.format(**locals()).split()
        with open(target, 'w') as out:
            out.writelines(fileinput.input(sources))

    # generate LPS

    lps_target = "franklin_{ring}_{l}-{version}.lps".format(**locals())

    if not os.path.isfile(lps_target):
        print(BOLD + "Generating {lps_target}...".format(**locals()) + NORMAL)
        sh.mcrl22lps("-Dfvn", target, lps_target, _err=sys.stdout)


def gen_hesselink(data, version):
    target = "hesselink_{data}-{version}.mcrl2".format(**locals())

    # generate mCRL2 file

    if not os.path.isfile(target):
        print(BOLD + "Generating {target}...".format(**locals()) + NORMAL)
        sources = 'data{data}.mcrl2 hesselink-{version}.mcrl2'.format(**locals()).split()
        with open(target, 'w') as out:
            out.writelines(fileinput.input(sources))

    # generate LPS

    lps_target = "hesselink_{data}-{version}.lps".format(**locals())

    if not os.path.isfile(lps_target):
        print(BOLD + "Generating {lps_target}...".format(**locals()) + NORMAL)
        sh.mcrl22lps("-Dfvn", target, lps_target, _err=sys.stdout)


def gen_WMS():
    # generate LPS

    if not os.path.isfile("WMS.lps"):
        print(BOLD + "Generating WMS.lps" + NORMAL)
        sh.lpsconstelm(sh.mcrl22lps("-Dfvn", "WMS.mcrl2", _piped=True, _err=sys.stdout), "-v", _out="WMS.lps", _err=sys.stdout)


def gen_ertms():
    # generate LPS

    if not os.path.isfile("ertms-b.lps"):
        print(BOLD + "Generating ertms-b.lps" + NORMAL)
        sh.lpsparelm(sh.lpsconstelm(sh.mcrl22lps("-Dfvn", "INESS_iter1_r468.mcrl2", _piped=True, _err=sys.stdout), "-v", _piped=True, _err=sys.stdout), '-v', _out="ertms-b.lps", _err=sys.stdout)


def gen_lhc(num):
    target = "lhc_{num}-b.mcrl2".format(**locals())

    # generate mCRL2 file

    if not os.path.isfile(target):
        print(BOLD + "Generating {target}...".format(**locals()) + NORMAL)
        sources = 'data.mcrl2 act.mcrl2 sector.mcrl2 chamber.mcrl2 wheel.mcrl2 wheel_tm.mcrl2 Composition.mcrl2 initWheel{num}.mcrl2'.format(**locals()).split()
        with open(target, 'w') as out:
            out.writelines(fileinput.input(sources))

    # generate LPS

    lps_target = "lhc_{num}-b.lps".format(**locals())

    if not os.path.isfile(lps_target):
        print(BOLD + "Generating {lps_target}...".format(**locals()) + NORMAL)
        sh.lpsparelm(sh.lpsconstelm(sh.mcrl22lps("-Dfvn", target, _piped=True, _err=sys.stdout), "-v", _piped=True), '-v', _out=lps_target, _err=sys.stdout)


def gen_all():
    for d,v in product([2, 3, 4], ['b', 'e']):
        gen_abp(d, v)

    for d,v in product([2, 3, 4], ['b', 'e']):
        gen_onebit(d, v)

    for d,l,n,v in product([2, 3, 4], [3, 4], [3, 4], ['b', 'e']):
        # data, lists, retries, versions
        gen_brp(d, l, n, v)

    for d,w,v in product([2, 3, 4], [2, 3, 4], ['b', 'e']):
        # data, window, version
        gen_swp(d, w, v)

    for r,v in product([2, 3, 4, 5], ['b', 'e']):
        gen_dkr(r, v)

    for r,l,v in product([2, 3, 4, 5], [2, 3, 4, 5], ['b', 'e']):
        if r >= l: gen_franklin(r, l, v)

    for d,v in product([2, 3, 4, 5], ['b', 'e']):
        gen_hesselink(r, v)

    gen_WMS()

    for s in [2, 3, 4]:
        gen_lhc(s)

    gen_ertms()


if __name__ == "__main__":
    gen_all()
