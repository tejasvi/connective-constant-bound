# gen_all_k26f.py OUT: write every generated module of the K26F proof into OUT with tools/gen_k26f.py's functions:
# the 48,024 shard modules (B = 20000, G = 100), the 188 part modules and the root.
import os, runpy, sys
out = sys.argv[1]
sys.argv = ["gen_k26f.py", out, "parts", "20000", "256"]
g = runpy.run_path(os.path.join(os.path.dirname(os.path.abspath(__file__)), "gen_k26f.py"), run_name="genall")
M = (g["NT"] + 20000 - 1) // 20000
for k in range(M):
    g["gen_shard"](k, 20000, 100)
print("shards", M)
