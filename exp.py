#!/usr/bin/env python
from __future__ import print_function
from contextlib import contextmanager
import os
import sys
import re
import itertools
from tabulate import tabulate

# import framework
from expfw import Experiment, ExperimentEngine, fixnan, online_variance

@contextmanager
def cd(newdir):
    prevdir = os.getcwd()
    os.chdir(os.path.expanduser(newdir))
    try:
        yield
    finally:
        os.chdir(prevdir)

class ExperimentMC(Experiment):
    """
    Base class for the multi-core tool
    """
    def parse_log(self, contents):
        res = {}
        s = re.compile(r'Time for computing the bisimulation relation: ([\d\.,]+)').findall(contents)
        if len(s) != 1: return None
        res['time'] = float(s[0].replace(',',''))
        s = re.compile('Time needed for signature computation: ([\d\.,]+)').findall(contents)
        if len(s) == 1: res['tsig'] = float(s[0].replace(',',''))
        s = re.compile('Time needed for partition refinement: ([\d\.,]+)').findall(contents)
        if len(s) == 1: res['tref'] = float(s[0].replace(',',''))
        s = re.compile('Time for signature computation: ([\d\.,]+)').findall(contents)
        if len(s) == 1: res['tsig'] = float(s[0].replace(',',''))
        s = re.compile('Time for partition refinement: ([\d\.,]+)').findall(contents)
        if len(s) == 1: res['tref'] = float(s[0].replace(',',''))
        s = re.compile('Time for computing the quotient of the transition relation: ([\d\.,]+)').findall(contents)
        if len(s) == 1: res['tquot'] = float(s[0].replace(',',''))
        s = re.compile('New Markov transition relation: ([\d\.,]+) transitions, ([\d\.,]+) MTBDD nodes').findall(contents)
        if len(s) == 1: res['newmarkov'] = int(s[0][1].replace(',',''))
        s = re.compile('New interactive transition relation: ([\d\.,inf]+) transitions, ([\d\.,]+) MTBDD nodes').findall(contents)
        if len(s) == 1: res['newtrans'] = int(s[0][1].replace(',',''))
        return res


class ExperimentRW(Experiment):
    """
    Base class for Ralf Wimmer's tools

    Only parses total time done by default.
    """
    def parse_log(self, contents):
        res = {}
        s = re.compile(r'Time for computing the bisimulation relation =[\s]*([\d\.]+)').findall(contents)
        if len(s) != 1: return None
        res['time'] = float(s[0].replace(',',''))
        return res


def float_str(f):
    if str(f) == 'nan': return '--'
    else: return str(int(f))

class ExperimentLTS_s(ExperimentMC):
    def __init__(self, name, workers, model, blocks_first=True):
        self.name = "{}-s-{}".format(name, workers)
        self.call = ["./sigrefmc", "-b", "2", "-w", str(workers)] + model
        if blocks_first: self.call += ["--blocks-first"]

class ExperimentLTS_s2(ExperimentMC):
    def __init__(self, name, workers, model, blocks_first=True):
        self.name = "{}-s2-{}".format(name, workers)
        self.call = ["./sigrefmc", "-b", "3", "-w", str(workers)] + model
        if blocks_first: self.call += ["--blocks-first"]        

class ExperimentLTS_s3(ExperimentMC):
    def __init__(self, name, workers, model, blocks_first=True):
        self.name = "{}-s3-{}".format(name, workers)
        self.call = ["./sigrefmc", "-b", "4", "-w", str(workers)] + model
        if blocks_first: self.call += ["--blocks-first"]

class LTSExperiments(object):
    def __init__(self, blocks_first=True):
        self.mcs_1 = {}
        self.mcs_48 = {}
        self.mcs2_1 = {}
        self.mcs2_48 = {}
        self.mcs3_1 = {}
        self.mcs3_48 = {}


        for m,a in self.models:
            self.mcs_1[m] = ExperimentLTS_s(name=m, workers=1, model=a, blocks_first=blocks_first)
            self.mcs_48[m] = ExperimentLTS_s(name=m, workers=48, model=a, blocks_first=blocks_first)
            self.mcs2_1[m] = ExperimentLTS_s2(name=m, workers=1, model=a, blocks_first=blocks_first)
            self.mcs2_48[m] = ExperimentLTS_s2(name=m, workers=48, model=a, blocks_first=blocks_first)
            self.mcs3_1[m] = ExperimentLTS_s3(name=m, workers=1, model=a, blocks_first=blocks_first)
            self.mcs3_48[m] = ExperimentLTS_s3(name=m, workers=48, model=a, blocks_first=blocks_first)
            
    def __iter__(self):
        s1 = [v for k,v in self.mcs_1.items()]
        s2 = [v for k,v in self.mcs_48.items()]
        s3 = [v for k,v in self.mcs2_1.items()]
        s4 = [v for k,v in self.mcs2_48.items()]
        s5 = [v for k,v in self.mcs3_1.items()]
        s6 = [v for k,v in self.mcs3_48.items()]
        return itertools.chain(s1, s2, s3, s4, s5, s6)

    models = [
        ("kanban01", ["models/kanban01.xlts"]),
        ("kanban02", ["models/kanban02.xlts"]),
        ("kanban03", ["models/kanban03.xlts"]),
        ("kanban04", ["models/kanban04.xlts"]),
        ("kanban05", ["models/kanban05.xlts"]),
        ("kanban06", ["models/kanban06.xlts"]),
    ]

    s1 = {
        "kanban01-s": (256, 148),
        "kanban02-s": (63772, 5725),
        "kanban03-s": (1024240, 85356),
        "kanban04-s": (16020316, 778485),
        "kanban05-s": (16772032, 5033631),
        "kanban06-s": (264515056, 25293849),
    }

    def analyse(self, results, timeouts):
        data = {}
        for name in [name for name, fn in self.models]:
            r = {}
            r['n_mc_1'], r['mc_1'] = online_variance([v['time'] for n, v in results if n==self.mcs_1[name].name])[0:2]
            r['n_mc_48'], r['mc_48'] = online_variance([v['time'] for n, v in results if n==self.mcs_48[name].name])[0:2]
            r['n_mc2_1'], r['mc2_1'] = online_variance([v['time'] for n, v in results if n==self.mcs2_1[name].name])[0:2]
            r['n_mc2_48'], r['mc2_48'] = online_variance([v['time'] for n, v in results if n==self.mcs2_48[name].name])[0:2]
            r['n_mc3_1'], r['mc3_1'] = online_variance([v['time'] for n, v in results if n==self.mcs3_1[name].name])[0:2]
            r['n_mc3_48'], r['mc3_48'] = online_variance([v['time'] for n, v in results if n==self.mcs3_48[name].name])[0:2]
            # r['sig_1'] = online_variance([v['tsig'] for n, v in results if n==self.mcs_1[name].name])[1]
            # r['sig_48'] = online_variance([v['tsig'] for n, v in results if n==self.mcs_48[name].name])[1]
            # r['ref_1'] = online_variance([v['tref'] for n, v in results if n==self.mcs_1[name].name])[1]
            # r['ref_48'] = online_variance([v['tref'] for n, v in results if n==self.mcs_48[name].name])[1]
            if r['mc_48'] > 0: r['speedup1'] = r['mc_1']/r['mc_48']
            else: r['speedup1'] = float('nan')
            if r['mc2_48'] > 0: r['speedup2'] = r['mc2_1']/r['mc2_48']
            else: r['speedup2'] = float('nan')
            if r['mc3_48'] > 0: r['speedup3'] = r['mc3_1']/r['mc3_48']
            else: r['speedup3'] = float('nan')
            data[name+"-s"] = r
        self.data = data
        return data

    def report(self, res=None):
        if res is None: res = self.data

        table = []
        for name in sorted(res.keys()):
            r = res[name]
            table.append([name,
                          "{}".format(r['n_mc_1']),
                          "{}".format(r['n_mc_48']),
                          "{}".format(r['n_mc2_1']),
                          "{}".format(r['n_mc2_48']),
                          "{}".format(r['n_mc3_1']),
                          "{}".format(r['n_mc3_48']),
                          "{:<6.2f}".format(r['mc_1']),
                          "{:<6.2f}".format(r['mc_48']),
                          "{:<6.2f}".format(r['mc2_1']),
                          "{:<6.2f}".format(r['mc2_48']),
                          "{:<6.2f}".format(r['mc3_1']),
                          "{:<6.2f}".format(r['mc3_48']),
                          "{:<6.2f}".format(r['speedup1']),
                          "{:<6.2f}".format(r['speedup2']),
                          "{:<6.2f}".format(r['speedup3']),
                          ])

        headers = ["Model      ","N_1","N_48","N2_1","N2_48","N2_1","N2_48", "  T_1", "  T_48", " T2_1", " T2_48", " T3_1", " T3_48","Speedup1", "Speedup2", "Speedup3"]
        print(tabulate(table, headers))

    def report_latex(self, out):
        res = self.data

        table = []
        for name in sorted(res.keys()):
            r = res[name]
            table.append([name,
                          "{}".format(self.s1[name][0]) if name in self.s1 else "",
                          "{}".format(self.s1[name][1]) if name in self.s1 else "",
                          "{:<6.2f}".format(r['mc_1']),
                          "{:<6.2f}".format(r['mc_48']),
                          "{:<6.2f}".format(r['mc2_1']),
                          "{:<6.2f}".format(r['mc2_48']),
                          "{:<6.2f}".format(r['mc3_1']),
                          "{:<6.2f}".format(r['mc3_48']),
                          "{:<6.2f}".format(r['speedup1']),
                          "{:<6.2f}".format(r['speedup2']),
                          "{:<6.2f}".format(r['speedup3']),
                          ])

        headers = ["Model", "States", "Blocks", "$T_{1}$", "$T_{48}$", "$T2_{1}$", "$T2_{48}$", "$T3_{1}$", "$T3_{48}$", "Speedup1", "Speedup2", "Speedup3"]
        table = fixnan(table)
        out.write(tabulate(table, headers, tablefmt='latex_booktabs'))


# signature refinement experiments
lts = LTSExperiments()

sr = ExperimentEngine(outdir='out', timeout=3600)
sr += lts

if __name__ == "__main__":
    if len(sys.argv) > 1:
        if sys.argv[1] == 'run':
            sr.run_experiments()
        elif sys.argv[1] == 'report':
            n, no, results, timeouts = sr.get_results()
            lts.analyse(results, timeouts)

            lts.report()
            print()

            with open('results_lts.tex', 'w') as f:
                lts.report_latex(f)