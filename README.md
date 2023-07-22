# 2023-schedule

A MiniZinc model to compute the school schedule.

Develop with:

```
# download google sheet to data/sheet.csv
poetry run python3 csv2json.py < data/sheet.csv > data/sheet.json
ls model.mzn | entr minizinc --solver or-tools --time-limit 30000 --statistics model.mzn data/sheet.json
```

Export CSV with:

```
poetry run python3 main.py < data/sheet.json > data/output.json
```
