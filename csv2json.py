# read CSV from stdin
# accumulate first col into json field "people"
# write JSON to stdout

import csv
import json
import sys

def mkMark(s):
    if s == '1':
        return 'M'
    elif s == '+':
        return 'O'
    else:
        return 'O'

# read CSV from stdin
reader = csv.reader(sys.stdin)
next(reader) # skip header

courses = next(reader)[3:]
lengths = [int(x) for x in next(reader)[3:]]

people = []
marks = []
for row in reader:
    if row[0]: # nickname is not empty
        people.append(row[0])
        marks.append([mkMark(x) for x in row[3:]])

# write JSON to stdout
json.dump({
    "courses": courses,
    "lengths": lengths,
    "people": people,
    "marks": marks
    },
    sys.stdout)