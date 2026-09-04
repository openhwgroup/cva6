import re

def read_line(fd, line_nb):
    ret = fd.readline()
    line_nb += 1
    while (ret.startswith("UVM_") or ret.startswith("[SPIKE]") or
           ret.startswith("*** [rvfi_tracer") or ret.startswith("CPU time used:") or
           ret.startswith("Wall clock time passed:")):
        ret = fd.readline()
        line_nb += 1
    return ret, line_nb

def compare_text_traces(file1, file2, name1, name2, log):
    """Compare two generic text file"""
    matched_cnt = 0
    mismatch_cnt = 0
    file1_index = 0
    file2_index = 0

    if log:
        fd = open(log, 'a+')
    else:
        fd = sys.stdout

    fd.write("{} : {}\n".format(name1, file1))
    fd.write("{} : {}\n".format(name2, file2))
    with open(file1, "r") as fd1, open(file2, "r") as fd2:
        while (True):
            line1, file1_index = read_line(fd1, file1_index)
            line2, file2_index = read_line(fd2, file2_index)
            if (line1 == "" and line2 == ""):
                break
            if line1 != line2:
                mismatch_cnt += 1
                fd.write("\nMismatch[%s]:\n" % mismatch_cnt)
                if (line1 == ""):
                    fd.write("%s : <EOF>\n" % name1)
                else:
                    fd.write("{}[{}] : {}\n".format(name1, file1_index, line1.strip()))
                if (line2 == ""):
                    fd.write("%s : <EOF>\n" % name2)
                else:
                    fd.write("{}[{}] : {}\n".format(name2, file2_index, line2.strip()))
            else:
                matched_cnt += 1

    if mismatch_cnt == 0:
        compare_result = "[PASSED]: {} matched\n".format(matched_cnt)
    else:
        compare_result = "[FAILED]: {} matched, {} mismatch\n".format(
            matched_cnt, mismatch_cnt)
    fd.write(compare_result + "\n")
    if log:
        fd.close()
    return compare_result

def compare_text_regexp(file, ref_file, name, log):
    """Compare two generic text file"""
    matched_cnt = 0
    mismatch_cnt = 0
    file_index = 0
    ref_index = 0

    if log:
        fd = open(log, 'a+')
    else:
        fd = sys.stdout

    fd.write("{} : {}\n".format(name, file))
    fd.write("Reference : %s\n" % ref_file)
    with open(file, "r") as fd1, open(ref_file, "r") as fd2:
        while (True):
            line, file_index = read_line(fd1, file_index)
            regexp, ref_index = read_line(fd2, ref_index)
            if (line == "" and regexp == ""):
                break
            if re.match(regexp.strip(), line.strip()) is None:
                mismatch_cnt += 1
                fd.write("\nMismatch[%s]:\n" % mismatch_cnt)
                if (line == ""):
                    fd.write("%s : <EOF>\n" % name)
                else:
                    fd.write("{}[{}] : {}\n".format(name, file_index, line.strip()))
                if (regexp == ""):
                    fd.write("%s : <EOF>\n" % name2)
                else:
                    fd.write("Expected[{}] : {}\n".format(ref_index, regexp.strip()))
            else:
                matched_cnt += 1

    if mismatch_cnt == 0:
        compare_result = "[PASSED]: {} matched\n".format(matched_cnt)
    else:
        compare_result = "[FAILED]: {} matched, {} mismatch\n".format(
            matched_cnt, mismatch_cnt)
    fd.write(compare_result + "\n")
    if log:
        fd.close()
    return compare_result
