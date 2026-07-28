import os
import sys
import yaml
import report_builder as rb

INPUT_DIR = str(sys.argv[1])

# merged_data = {}

energy_metric = rb.TableMetric("Energy results")
area_metric = rb.TableMetric("Area results")
aes_cycle_metric = rb.TableMetric("Aes results")
dhrystone_cycle_metric = rb.TableMetric("Dhrystone results")
area_found = False
energy_found = False
bench_aes_found = False
bench_dhrystone_found = False

for filename in os.listdir(INPUT_DIR):
    if ("area_check" in filename) and (filename != "merge_statistics.yml"):
        print(f"found: {filename}")
        area_found = True
        config = filename.split("___")[1].replace("_.yml", "")
        filepath = os.path.join(INPUT_DIR, filename)
        with open(filepath, "r", encoding="utf-8") as f:
            data = yaml.safe_load(f)

        area = None
        # Look into metrics
        metrics = data.get("metrics", [])
        for metric in metrics:
            values = metric.get("value", [])
            for e in values:
                if not isinstance(e, dict):
                    continue
                col = e.get("col", [])
                if isinstance(col, list) and len(col) == 2:
                    if col[0] == "Total area":
                        area_val = col[1].replace("Gates", "").strip()
                        area = int(area_val)

        # merged_data[config] = {"area": area}
        area_metric.add_value(config, area)
    if ("power_check" in filename) and (filename != "merge_statistics.yml"):
        print(f"found: {filename}")
        energy_found = True
        config = filename.split("___")[1].replace("_.yml", "")
        filepath = os.path.join(INPUT_DIR, filename)
        with open(filepath, "r", encoding="utf-8") as f:
            data = yaml.safe_load(f)

        energy = None
        # Look into metrics
        metrics = data.get("metrics", [])
        for metric in metrics:
            values = metric.get("value", [])
            for e in values:
                if not isinstance(e, dict):
                    continue
                col = e.get("col", [])
                if isinstance(col, list) and len(col) == 2:
                    if col[0] == "Total Energy":
                        energy_val = col[1].replace("Je-15", "").strip()
                        energy = int(float(energy_val))

        # merged_data[config] = {"area": area}
        energy_metric.add_value(config, energy)
    if ("smoke_bench___aes" in filename) and (filename != "merge_statistics.yml"):
        print(f"found: {filename}")
        bench_aes_found = True
        # name is : smoke_bench___aes__cv32a6*x_.yml
        config = filename.split("___")[1]
        config = config.split("__")[1].replace("_.yml", "")
        filepath = os.path.join(INPUT_DIR, filename)
        with open(filepath, "r", encoding="utf-8") as f:
            data = yaml.safe_load(f)

        cycle = None
        # Look into metrics
        metrics = data.get("metrics", [])
        for metric in metrics:
            print(metric)
            values = metric.get("value", [])
            print(values)
            for e in values:
                print(e)
                if not isinstance(e, dict):
                    continue
                col = e.get("col", [])
                print(col)
                if isinstance(col, list) and len(col) == 2:
                    if col[0] == "cycles":
                        cycle = int(col[1])

        # merged_data[config] = {"area": area}
        print(f"config: {config}, cycle: {cycle}")
        aes_cycle_metric.add_value(config, cycle)
    if ("smoke_bench___dhrystone" in filename) and (filename != "merge_statistics.yml"):
        print(f"found: {filename}")
        bench_dhrystone_found = True
        # name is : smoke_bench___dhrystone__cv32a6*x_.yml
        config = filename.split("___")[1]
        config = config.split("__")[1].replace("_.yml", "")
        print(config)
        filepath = os.path.join(INPUT_DIR, filename)
        with open(filepath, "r", encoding="utf-8") as f:
            data = yaml.safe_load(f)

        cycle = None
        # Look into metrics
        metrics = data.get("metrics", [])
        for metric in metrics:
            values = metric.get("value", [])
            for e in values:
                if not isinstance(e, dict):
                    continue
                col = e.get("col", [])
                if isinstance(col, list) and len(col) == 2:
                    if col[0] == "cycles":
                        cycle = int(col[1])

        # merged_data[config] = {"area": area}
        dhrystone_cycle_metric.add_value(config, cycle)


report = rb.Report()
if area_found:
    report.add_metric(area_metric)
else:
    report.fail()
    report.add_metric(area_metric)

if energy_found:
    report.add_metric(energy_metric)
else:
    report.fail()
    report.add_metric(energy_metric)

if bench_aes_found:
    report.add_metric(aes_cycle_metric)
else:
    report.fail()
    report.add_metric(aes_cycle_metric)

if bench_dhrystone_found:
    report.add_metric(dhrystone_cycle_metric)
else:
    report.fail()
    report.add_metric(dhrystone_cycle_metric)

report.dump()
