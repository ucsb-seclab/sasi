import os
import sys
from parsing_utils import parse_output_file
bench_dir = sys.argv[1]
bench_mark_name = 'SPEC_2000.186.crafty'
script_path = os.path.dirname(os.path.realpath(__file__))
shell_script = os.path.join(script_path, 'run_SPEC_2000.186.crafty.sh')
output_file_path = 'run_SPEC_2000.186.crafty.out'
for cf in os.listdir(bench_dir):
    cfp = os.path.join(bench_dir, cf)
    if cf.endswith('.c'):
        os.system(shell_script + ' ' + cfp + ' -compare-strided-range-analyses 2>>' + output_file_path)

strided_time, wrapped_time, total_intervals, strided_recovered, wrapped_recovered, strided_more_precise, wrapped_more_precise, wrapped_alias_impr, strided_alias_impr = parse_output_file(output_file_path)

print bench_mark_name,strided_time, wrapped_time, total_intervals, strided_recovered, wrapped_recovered, strided_more_precise, wrapped_more_precise, wrapped_alias_impr, strided_alias_impr

