import json
import csv
import sys
from datetime import timedelta
from minizinc import Instance, Model, Solver

model = Model(files=["./model.mzn"])
gecode = Solver.lookup("gecode")
instance = Instance(gecode, model)

data = json.load(sys.stdin)

instance["people"] = data["people"]
instance["courses"] = data["courses"]
instance["lengths"] = data["lengths"]
instance["marks"] = data["marks"]

result = instance.solve(timeout=timedelta(milliseconds=100))

print(result.status, file=sys.stderr)
print(result, file=sys.stderr)

writer = csv.writer(sys.stdout)
writer.writerow(["nickname", "course1", "course2", "course3"])
for person, courses in zip(data["people"], result["people2courses"]):
    writer.writerow([person] + list(courses))