import os
BENCHMARK_ROOT='spec_benchmarks/'
ALL_BENCHMARKS = [('SPEC_2000.256.bzip2', 'bzip2-1.0.6'),('SPEC_2000.186.crafty', 'crafty'),('SPEC_2000.164.gzip','gzip-1.8'),('SPEC_2006.456.hmmer','hmmer-3.1b2-linux-intel-x86_64'), ('SPEC_2000.197.parser','link-4.1b'), ('SPEC_2000.175.vpr', 'vpr_430'), ('SPEC_2006.462.libquantum', 'libquantum-1.0.0')]

for curr_bench, fol_name in ALL_BENCHMARKS:
    print "[+] Running Benchmark:" + curr_bench
    bench_dir = os.path.abspath(os.path.join(BENCHMARK_ROOT, fol_name))
    print 'python ' + os.path.join('run_scripts', 'run_' + curr_bench + '.py') + ' ' + bench_dir
    os.system('python ' + os.path.join('run_scripts', 'run_' + curr_bench + '.py') + ' ' + bench_dir)
            

