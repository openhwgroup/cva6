import numpy as np
import matplotlib.pyplot as plt
import sys

if len(sys.argv) < 2:
    print("Usage: analyze_traces_quick.py <traces.npy> [target_index]")
    sys.exit(1)

arr = np.load(sys.argv[1])  # shape (ntraces, evset_size)
ntraces, ev = arr.shape
target = int(sys.argv[2]) if len(sys.argv) > 2 else 0

# histogram of target column
vals = arr[:, target]
plt.figure()
plt.hist(vals, bins=60)
plt.xlabel('cycles')
plt.ylabel('count')
plt.title(f'Histogram probe times (index {target})')
plt.savefig('hist_target.png', dpi=300)
print("Saved hist_target.png")

# simple heatmap of means across trials grouped by secret index if available
# If you had secrets array parallel to traces, load it and do per-secret means.
# For now show full heatmap (trials x evset index)
plt.figure(figsize=(6,4))
plt.imshow(arr.T, aspect='auto', origin='lower')
plt.colorbar(label='cycles')
plt.xlabel('trial')
plt.ylabel('evset index')
plt.title('Probe times heatmap (evset index vs trial)')
plt.savefig('heatmap_trials_idx.png', dpi=300)
print("Saved heatmap_trials_idx.png")

# quick MI estimate between discretized times and trial index modulo some small base (if you used NUM_SECRETS)
# if NUM_SECRETS used, compute pseudo-secret:
NUM_SECRETS = None
# try infer: if number of distinct trial groups small, attempt MI per index
for i in range(ev):
    x = arr[:, i]
    # discretize
    bins = np.histogram_bin_edges(x, bins=30)
    xq = np.digitize(x, bins)
    # attempt to infer secret groups by trial % k (if k provided)
    # skip MI printing unless user supplies secrets
print("Done.")