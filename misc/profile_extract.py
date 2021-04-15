import os
import json

def load_json(path):
    with open(path, "r") as file:
        return json.load(file)

def error(cli, msg):
    print(cli)
    print("Error: %s" % msg)
    return 1

def validate(data):
    if not isinstance(data, dict): return False
    if len(data) != 2: return False
    if "nodes" not in data: return False
    nodes = data["nodes"]
    if not isinstance(nodes, list): return False
    if len(nodes) == 0: return True
    node = nodes[0]
    if not isinstance(node, dict): return False
    if len(node) != 11: return False
    if "id" not in node: return False
    if "kind" not in node: return False
    if "landmark_id" not in node: return False
    if "name" not in node: return False
    if "location" not in node: return False
    if "calls" not in node: return False
    if "time" not in node: return False
    if "sons" not in node: return False
    if "sys_time" not in node: return False
    if "allocated_bytes" not in node: return False
    if "distrib" not in node: return False
    return True

def process(data):
    nodes = data["nodes"]
    node_count = len(nodes)
    times = [node["time"] for node in nodes]
    result = times.copy()
    for node in nodes:
        node_id = node["id"]
        for child_id in node["sons"]:
            result[node_id] -= times[child_id]
    return nodes[0]["time"], [ {
        "name": node["name"],
        "calls": node["calls"],
        "time": result[node["id"]]
        } for node in nodes]

def report(total_time, result):
    def _time(item): return item["time"]
    def _row(node):
        name = node["name"]
        calls = node["calls"]
        time_total = node["time"]
        time_per_call = ((time_total / max(calls, 1.0)) / total_time) * 100.0
        time_total_percent = (time_total / total_time) * 100.0
        return (
            name,
            str(calls),
            ("%.4f" % time_per_call).replace('.', ','),
            ("%.4f" % time_total_percent).replace('.', ',')
        )
    result.sort(key=_time, reverse=True)
    csv = "'Name'; 'Calls'; 'Time Per Call'; 'Time Total'\n"
    for node in result:
        csv += "'%s'; %s; %s; %s\n" % _row(node)
    print(csv)

def main(args):
    cli = args[0]
    if len(args) != 2:
        return error(cli, "Expected an argument!")

    # Parse file path argument
    path = args[1]
    if not os.path.exists(path):
        return error(cli, "Argument is not a file path!")

    # Load profile data
    data = load_json(path)
    if not validate(data):
        return error(cli, "File is not a valid Landmarks profile!")

    # Process profile data
    total_time, result = process(data)

    # Print results
    report(total_time, result)

    # Done
    return 0

if __name__ == '__main__':
    import sys
    sys.exit(main(sys.argv))
