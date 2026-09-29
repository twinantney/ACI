
import numpy as np
from PrimeRuntimeV4_backup import Node, Policy

class StochasticResonanceNode(Node):
    def __init__(self, nid, noise_level=0.01):
        super().__init__(nid)
        self.noise_level = noise_level

    def apply_ssr(self, state_vec):
        noise = np.random.normal(0, self.noise_level, state_vec.shape)
        return self.policy.act(state_vec + noise)

def sync_phase_17(nodes, dt):
    for n in nodes:
        n.state.u = n.apply_ssr(np.concatenate([n.state.x, n.state.f]))
        n.state.x += dt * (n.state.u + n.state.f)
