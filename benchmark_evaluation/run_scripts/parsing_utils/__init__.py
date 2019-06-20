import os
def parse_output_file(target_outfile):
    to_ret = ()
    strided_time = 0.0
    wrapped_time = 0.0
    wrapped_more_precise = 0
    strided_more_precise = 0
    wrapped_recovered = 0
    strided_recovered = 0
    total_intervals = 0
    wrapped_alias_impr = 0
    strided_alias_impr = 0
    lines = open(target_outfile, 'r').readlines()
    for curr_line in lines:
        curr_line = curr_line.strip()
        if not curr_line:
            continue
        if '# tracked intervals                         :' in curr_line:
            total_intervals += int(curr_line.split('# tracked intervals                         : ')[1].strip())
        if 'Time:Strided=' in curr_line:
            strided_time += float(curr_line.split('Time:Strided=')[1].strip())
        if 'Time:Wrapped=' in curr_line:
            wrapped_time += float(curr_line.split('Time:Wrapped=')[1].strip())
        if '# proper wrapped intervals                : ' in curr_line:
            wrapped_recovered += int(curr_line.split('# proper wrapped intervals                : ')[1].strip())
        if '# proper Strided wrapped intervals                  : ' in curr_line:
            strided_recovered += int(curr_line.split('# proper Strided wrapped intervals                  : ')[1].strip())
        if '# strided wrapped < wrapped                       : ' in curr_line:
            strided_more_precise += int(curr_line.split('# strided wrapped < wrapped                       : ')[1].split()[0].strip())
        if '# wrapped < strwrapped                       : ' in curr_line:
            wrapped_more_precise += int(curr_line.split('# wrapped < strwrapped                       : ')[1].split()[0].strip())
        if '# Wrapped Alias Improved:' in curr_line:
            wrapped_alias_impr += int(curr_line.split("Improved:")[1].strip())
        if '# Strided Alias Improved:' in curr_line:
            strided_alias_impr += int(curr_line.split("Improved:")[1].strip()) 
    to_ret = (strided_time, wrapped_time, total_intervals, strided_recovered, wrapped_recovered, strided_more_precise, wrapped_more_precise, wrapped_alias_impr, strided_alias_impr)
    return to_ret
        
