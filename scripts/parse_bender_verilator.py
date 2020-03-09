import json

sources_file = "scripts/sources.json"

with open(sources_file) as f:
    x=json.load(f)


output_dir = {
    "defines":      [],
    "files":        [],
    "include_dirs": []
}

for dict in x:

    for define in dict["defines"]:
        if define not in output_dir["defines"]:
            output_dir["defines"].append(define)

    for file in dict["files"]:
        if file not in output_dir["files"]:
            output_dir["files"].append(file)

    for include_dir in dict["include_dirs"]:
        if include_dir not in output_dir["include_dirs"]:
            output_dir["include_dirs"].append(include_dir)

output_string = ""

exclude = [".vhd", "_tb", "tb_", "test/", "_test.", "tc_clk", "pad", "_latency"]

for file in output_dir["files"]:
    include = True
    for excl in exclude:
        if excl in file:
            include = False
    if "res_tbl" in file:
        include = True
    if include:
        output_string = output_string + "{} ".format(file)



for define in output_dir["defines"]:
    output_string = output_string + "+define+{} ".format(define)

for include_dir in output_dir["include_dirs"]:
    output_string = output_string + "+incdir+{} ".format(include_dir)

print(output_string)