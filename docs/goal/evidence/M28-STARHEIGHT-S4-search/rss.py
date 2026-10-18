import subprocess, sys, resource, time
t=time.time()
r=subprocess.run(sys.argv[1:], capture_output=True, text=True)
print(r.stdout[-3000:], r.stderr[-2000:])
print("exit", r.returncode, "time %.1fs" % (time.time()-t), "maxrss_MiB", resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss//1024)
