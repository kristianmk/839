# Limits of the method: scripts and data for Section 7

Requirements: Python 3 with python-flint (FLINT/Arb), numpy, scipy.

Certified statements (ball arithmetic; the output of the commands below is in `certified.log`):

    python ceiling_certified.py new    trial_new.json          # Q*(f) < 0.83998, window of the paper
    python ceiling_certified.py new    trial_cell_new.json     # the cell "simple, double, simple, empty"
    python ceiling_certified.py paper1 trial_cell_paper1.json  # window of the first paper
    python ceiling_certified.py mt     trial_cell_mt.json      # Montgomery–Taylor window
    python ceiling_certified.py new    trial_new_range6.json 6 # frames of seven points
    python ceiling_certified.py new    trial_new_range8.json 8 # frames of nine points
    python ceiling_certified.py new    trial_new_range10.json 10 # frames of eleven points
    python variation_certified.py                              # V(f), B(f) and V/B
    python ceiling_line_certified.py trial_line_range7.json 7  # second window (critical line), frames of eight points
    python ceiling_line_certified.py trial_line_all.json       # second window, all pairs

`ceiling_certified.py` takes periodic trial states (labels and gaps, rounded to rationals),
encloses their period energies rigorously (Poisson summation for all pairs; finite sums of
values of K² for a finite range) and the constant C(f) by rigorous integration, chooses
rational weights, and checks the two inequalities used in the proof of the proposition on ceilings (span and energy).

Searches (floating point; they only propose trial states, nothing is proved by them):
`ground_state.py`, `ground_state2.py`, `ground_state3.py`. `figure_data.py` writes the data
of Figure 3.

`ceiling_line_certified.py` does the same for the critical-line problem of Theorem 1.3 (window `line`
in `ceiling_certified.py`; only simple points interact): for periodic states of simple points it
encloses the pair energy per period and checks `sum w (e - n + (2 - C) P) <= 0`, which gives
`(2 - C - b)/(1 - x) <= sum w n / sum w P` for every certificate `(x, b)` of that range.
