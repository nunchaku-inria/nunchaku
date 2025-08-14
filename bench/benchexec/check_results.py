import csv
import sys

def legal_deviation(val: str) -> bool:
    return val == "unknown" or val.startswith("TIMEOUT")

def validate_csv(filename: str):
    errors = []

    with open(filename, "r") as file:
        for _ in range(3):
            next(file, None)

        csv_reader = csv.reader(file, delimiter="\t")

        for row in csv_reader:
            expected = row[2].strip()
            result = row[3].strip()

            if expected != result and not legal_deviation(result):
                name = row[0].strip()
                errors.append(f"{name} should be '{expected}' but is '{result}'")

    if errors:
        print(f"Found errors:")
        for error in errors:
            print(f"  {error}")
        sys.exit(1)
    else:
        print("All test results are OK")
        sys.exit(0)

def main():
    validate_csv(sys.argv[1])

if __name__ == '__main__':
    main()
