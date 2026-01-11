import subprocess, yaml, os
import sys
from pathlib import Path
import smt

def main():
    with open(Path(__file__).resolve().parent / "dafny-ipm.yaml") as f:
        cfg = yaml.safe_load(f)

    dafnydll = cfg["programs"]["dafnyipmdll"]
    boogiedll = cfg["programs"]["boogiedll"]

    command = ""
    if len(sys.argv) == 3:
        command = sys.argv[2]
        if command != "--explore" and command != "--print-all":
            print(f"Error: command '{command}' is not recognized (expected --explore or --print-all).")
            sys.exit(1)

    if len(sys.argv) != 2 and len(sys.argv) != 3:
        print(f"Usage: {sys.argv[0]} <filename>")
        sys.exit(1)

    filepath = Path(sys.argv[1])
    if filepath.suffixes != ['.dfy']:
        print(f"Error: file '{filepath}' needs to be a Dafny source file (must end with \".dfy\").")
        sys.exit(1)

    if not filepath.exists():
        print(f"Error: file '{filepath}' does not exist.")
        sys.exit(1)

    bplfilepath = filepath.with_suffix('.bpl')
    smt2filepath = filepath.with_suffix('.smt2')

    print(f"STEP 1. Creating: {bplfilepath}")

    cmdline = ["dotnet", str(dafnydll), "-print:" + str(bplfilepath), str(filepath), "/noVerify"]
    print("Running " + " ".join(cmdline))
    dafnyresult = subprocess.run(cmdline)
    if dafnyresult.returncode != 0:
        print(f"Error: dafny could not process file '{filepath}'.")
        sys.exit(1)

    print(f"STEP 2. Creating: {smt2filepath}")

    cmdline = ["dotnet", str(boogiedll), "/timeLimit:1", "/trace", "/proverLog:" + str(smt2filepath), str(bplfilepath)]
    print("Running " + " ".join(cmdline))
    boogieresult = subprocess.run(cmdline)
    if boogieresult.returncode != 0:
        print(f"Error: boogie could not process file '{filepath}'.")
        sys.exit(1)

    print(f"STEP 3. Entering interactive mode")
    if command:
        smt.start_ipm(str(smt2filepath), command)
    else:
        smt.start_ipm(str(smt2filepath), )


if __name__ == "__main__":
    # Check for test mode first
    if len(sys.argv) >= 2 and sys.argv[1] == "--test":
        # Import test framework
        from test_framework import run_test_suite, test_specific_files

        if len(sys.argv) == 2:
            # Run all tests with default database path
            results = run_test_suite("database")
        else:
            # Run tests with specified database path
            results = run_test_suite(sys.argv[2])

        # Exit with appropriate code
        sys.exit(0 if all(r.success for r in results) else 1)

    elif len(sys.argv) >= 2 and sys.argv[1] == "--test-file":
        # Test specific files
        from test_framework import test_specific_files

        if len(sys.argv) < 3:
            print("Error: --test-file requires at least one file path")
            sys.exit(1)

        file_paths = sys.argv[2:]
        results = test_specific_files(file_paths)
        sys.exit(0 if all(r.success for r in results) else 1)

    else:
        # Normal mode - run main function
        main()