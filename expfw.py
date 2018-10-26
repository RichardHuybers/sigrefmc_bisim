#!/usr/bin/env python
from __future__ import print_function
import os
import sys
from subprocess32 import call, TimeoutExpired
import time
import random
import itertools


class Experiment(object):
    NOTDONE = 0
    DONE = 1
    TIMEOUT = 2

    def __init__(self, name=None, call=None):
        self.name = name
        self.call = call

    def parse_log(self, contents):
        """Parse the log file.

        Return None if not good, or a dict with the results otherwise.
        """
        return None

    def parse_logfile(self, filename):
        """Parse the log file.

        The open file handle is given in the parameter handle.

        Return None if the log file is not good
        Return a dict with the results otherwise.
        """
        if (os.path.isfile(filename)):
            with open(filename, 'r') as handle:
                return self.parse_log(handle.read())
        else:
            return None

    def get_status(self, filename):
        """Obtain the status of the experiment.

        Return a triple:
        (Experiment.DONE, time, res)
        (Experiment.TIMEOUT, time, None)
        (Experiment.NOTDONE, 0, None)
        """
        res = self.parse_logfile(filename)
        if res is not None: return Experiment.DONE, res['time'], res

        timeout_filename = "{}.timeout".format(filename)
        if (os.path.isfile(timeout_filename)):
            with open(timeout_filename, 'r') as to:
                return Experiment.TIMEOUT, int(to.read()), None

        return Experiment.NOTDONE, 0, None

    def run_experiment(self, timeout, filename):
        # get the status of the experiment
        status, value, db = self.get_status(filename)

        # if the experiment is done or the timeout >= current timeout, return
        if status == Experiment.DONE: return
        if status == Experiment.TIMEOUT and value >= int(timeout): return

        # remove output and timeout files
        if os.path.isfile(filename): os.unlink(filename)
        timeout_filename = "{}.timeout".format(filename)
        if os.path.isfile(timeout_filename): os.unlink(timeout_filename)

        # report that we are running the experiment
        print("Performing {}... ".format(self.name), end='')
        sys.stdout.flush()

        try:
            with open(filename, 'w+') as out:
                call(self.call, stdout=out, stderr=out, timeout=timeout)
        except KeyboardInterrupt:
            # if CTRL-C was hit, move the file
            new_filename = "{}.interrupted".format(filename)
            os.rename(filename, new_filename)
            print("interrupted!")
            sys.exit()
        except OSError:
            # OS error (probably missing executable), remove the log file
            os.unlink(filename)
            print("OS failure! (missing executable?)")
            sys.exit()
        except TimeoutExpired:
            # timeout hit, write current timeout value to .timeout file
            with open(timeout_filename, 'w') as to: to.write(str(timeout))
            print("timeout!")
        else:
            # experiment finished, either report done or not done...
            status, value, db = self.get_status(filename)
            if status == Experiment.DONE: print("done; {}!".format(value))
            else: print("not done!")

        # sleep 2 seconds to allow OS for breathing
        time.sleep(2)


class ExperimentEngine(object):
    def __init__(self, **kwargs):
        """Initialize a set of experiments.

        Parameters:
        - outdir
        - timeout
        """
        self.experiments = []
        if 'outdir' in kwargs: self.outdir = kwargs['outdir']
        else: self.outdir = 'out'
        if 'timeout' in kwargs: self.timeout = int(kwargs['timeout'])
        else: self.timeout = 1200

    def get_results(self):
        """Get all results.

        Return (n_iterations, n_not_done, results, timeouts)
        - results is a list of pairs (experiment, result)
        - timeouts is a list of pairs (experiment, timeout_value)
        """
        results = []
        timeouts = []
        no = 0

        for i in itertools.count():
            stop = True
            for e in self.experiments:
                status, value, db = e.get_status("{}/{}-{}".format(self.outdir, e.name, i))
                if not status == Experiment.NOTDONE: stop = False
                if status == Experiment.DONE: results.append((e.name, db))
                elif status == Experiment.TIMEOUT: timeouts.append((e.name, value))
                else: no += 1
            if stop: return i, no - len(self.experiments), results, timeouts

    def run_experiments(self):
        """Run experiments indefinitely.
        """
        if not os.path.exists(self.outdir): os.makedirs(self.outdir)
        for i in itertools.count():
            n, not_done, results, timeouts = self.get_results()
            print("In {} repetitions, {} succesful, {} timeouts, {} not done.".format(n, len(results), len(timeouts), not_done))

            print("Running iteration {}.".format(i))
            random.shuffle(self.experiments)
            for e in self.experiments:
                e.run_experiment(self.timeout, "{}/{}-{}".format(self.outdir, e.name, i))

    def __iadd__(self, other):
        if isinstance(other, Experiment):
            self.experiments.append(other)
            return self
        elif isinstance(other, ExperimentEngine):
            self.experiments.extend(other)
            return self
        elif hasattr(other, '__iter__'):
            for item in other:
                self += item
            return self
        else:
            return NotImplemented


def online_variance(data):
    n = 0
    mean = 0
    M2 = 0

    for x in data:
        n = n + 1
        delta = x - mean
        mean = mean + delta / n
        M2 = M2 + delta * (x - mean)

    if n < 1: return n, float('nan'), float('nan')
    if n < 2: return n, mean, float('nan')

    variance = M2 / (n - 1)
    return n, mean, variance


def fixnan(table):
    return [['--' if s.strip() == 'nan' else s for s in row] for row in table]
