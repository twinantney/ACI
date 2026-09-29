import sys
sys.path.append("/root/my_project")

from VerifyBridge import VerifyBridge
import numpy as np

def run_contagion_trace(total_steps=10000, checkpoint_every=500):
    bridge = VerifyBridge()

    for idx, node in enumerate(bridge.rt.nodes):
        node.state.x = np.array([float(idx * 0.5), float(-idx * 0.25), 10.0])
        node.state.p = np.array([5.0, -2.0, float(idx * 0.12)])
        node.state.f = np.array([1.0, 1.0, -1.0])

    dt = 0.02
    history = []

    for step in range(1, total_steps + 1):
        margins = [float(n.state.local_margin) for n in bridge.rt.nodes]
        vetoed = [i for i, m in enumerate(margins) if m < 0.05]

        for idx in vetoed:
            n = bridge.rt.nodes[idx]
            if len(n.links) > 0:
                for nb in n.links:
                    if n in nb.links:
                        nb.links.remove(n)
                n.links = []
            n.state.x *= 0.01
            n.state.u *= 0.01
            n.state.f *= 0.01
            n.state.p *= 0.01

        for idx in range(bridge.rt.node_count):
            n = bridge.rt.nodes[idx]
            if len(n.links) == 0 and float(np.linalg.norm(n.state.x)) == 0.0:
                p_idx = (idx - 1) % bridge.rt.node_count
                nx_idx = (idx + 1) % bridge.rt.node_count
                pn = bridge.rt.nodes[p_idx]
                nn = bridge.rt.nodes[nx_idx]
                if n not in pn.links:
                    pn.links.append(n)
                if n not in nn.links:
                    nn.links.append(n)
                n.links = [pn, nn]

        bridge.verified_step(dt)

        if step % checkpoint_every == 0:
            margins_now = [float(n.state.local_margin) for n in bridge.rt.nodes]
            vetoed_now = sorted(i for i, m in enumerate(margins_now) if m < 0.05)
            system_margin = min(margins_now)
            history.append((step, vetoed_now, system_margin))
            print(f"step {step:6d}: vetoed_count={len(vetoed_now):2d} vetoed={vetoed_now} system_margin={system_margin:.4f}")

    print("\n--- Summary ---")
    counts = [len(v) for _, v, _ in history]
    print(f"vetoed_count min={min(counts)} max={max(counts)} last={counts[-1]}")
    print(f"trend (first 5 checkpoints): {counts[:5]}")
    print(f"trend (last 5 checkpoints): {counts[-5:]}")

if __name__ == "__main__":
    run_contagion_trace(total_steps=10000, checkpoint_every=500)
