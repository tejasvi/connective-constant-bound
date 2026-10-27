# rtime.py CMD...: run CMD, then print "wall_s peak_rss_MB rc" (peak RSS of the child via RUSAGE_CHILDREN).
import resource, subprocess, sys, time
t = time.time()
rc = subprocess.call(sys.argv[1:])
ru = resource.getrusage(resource.RUSAGE_CHILDREN)
print("RTIME wall=%.1fs rss=%.0fMB rc=%d" % (time.time() - t, ru.ru_maxrss / 1024.0, rc), flush=True)
