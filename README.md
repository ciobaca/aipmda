# aipmda

An Interactive Proof Mode for Dafny


1. Install `dafny-ipm` from `github.com/dafny-ipm` (follow the usual installation instructions for Dafny).

2. Set a new virtual environment: `python3 -m venv .`

3. Activate the environment: `source bin/activate`

4. Install the following packages:

```
pip install pyyaml
pip install z3-solver
pip install colorama
pip install pip install prompt_toolkit
pip install pip install sexpdata
pip install pip install textual
```

5. Set the right paths in `dafny-ipm.yaml`

6. Run `python3 dafny-ipm.py database/ite_ex3.dfy` and type in the following:

```
check (x * (x + 1) % 2 == (x % 2) * ((x + 1) % 2))
:quit
```