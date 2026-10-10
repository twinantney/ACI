import sys
import time
import logging
import torch
import torch.nn.functional as F
from bionpc.model import FusedAPLNorm

logger = logging.getLogger("ApexEngine")

class ApexMasterTensorRuntime:
    """
    Production-grade GPU Tensor Runtime for the ACI Framework.
    Utilizes Biological Synaptic Decay (BioNPC) for physical friction 
    and dynamic Adjacency Matrix graphs for topological links.
    """
    def __init__(self, node_count=100000, device=None, damping_gain=0.95):
        self.N = node_count
        if device is None:
            self.device = 'cuda' if torch.cuda.is_available() else 'cpu'
        else:
            self.device = device
            
        logger.info(f"Allocating {self.N:,} nodes on {self.device.upper()}")
        
        # State Arrays [N, 3]
        self.x = torch.zeros((self.N, 3), device=self.device)
        self.p = torch.zeros((self.N, 3), device=self.device)
        self.f = torch.zeros((self.N, 3), device=self.device)
        self.u = torch.zeros((self.N, 3), device=self.device)
        
        # Scalar telemetry [N]
        self.margin = torch.ones(self.N, device=self.device)
        self.lyapunov_V = torch.zeros(self.N, device=self.device)
        self.y_spine = torch.zeros((self.N, 3), device=self.device)
        
        # 1D Ring Lattice Topology (Left/Right Active Edges)
        self.edge_left = torch.ones(self.N, device=self.device, dtype=torch.bool)
        self.edge_right = torch.ones(self.N, device=self.device, dtype=torch.bool)
        
        # Base Initializations
        idx = torch.arange(self.N, device=self.device, dtype=torch.float32)
        self.x[:, 0], self.x[:, 1], self.x[:, 2] = idx * 0.25, -idx * 0.12, 5.0
        self.p[:, 0], self.p[:, 1], self.p[:, 2] = 2.5, -1.0, idx * 0.08
        self.f[:] = torch.tensor([0.5, 0.5, -0.5], device=self.device)
        
        # Physical Constants
        self.MC2_LOCAL_RETAIN = 0.8
        self.MC2_GLOBAL_LEAK = 0.2
        self.MASS = 1.0
        
        # Synaptic Damping Engine
        self.synapse = FusedAPLNorm(d_model=3).to(self.device)
        with torch.no_grad():
            self.synapse.gain.fill_(damping_gain)
            
    def calculate_lyapunov(self) -> float:
        dx_sq = torch.sum((self.x - self.y_spine) ** 2, dim=1)
        dp_sq = torch.sum(self.p ** 2, dim=1)
        self.lyapunov_V = 0.5 * (dx_sq + dp_sq)
        return self.lyapunov_V.sum().item()

    def step(self, step_idx: int) -> dict:
        # 1. Kinematic Base Noise
        if 100 <= step_idx <= 300:
            self.x += torch.randn_like(self.x) * 0.85 * 0.02
            
        self.margin = 1.0 - torch.norm(self.u, dim=1)
        
        # 2. Hyper-Adversarial Strike
        if step_idx == 500:
            weakest = torch.argmin(self.margin)
            self.x[weakest] = 12000.0
            
        # 3. Lawson Overload
        if step_idx == 1000:
            self.margin[:] = 0.001

        # 4. ACI Magnetohydrodynamic mc2 Coupling cascade
        # x_d = x_d + 0.8 * delta
        # c_strength = 1.0 / (1.0 + 1.0) = 0.5
        # x_t = x_t + 0.2 * 0.5 * delta
        
        c_strength = 1.0 / (self.MASS + self.MASS)
        neighbor_leak = self.MC2_GLOBAL_LEAK * c_strength  # 0.1
        
        # Send U vectors across valid graph edges using PyTorch roll
        # If edge_right is True, node `i` sends to `i+1`. So node `i+1` receives from its left (shift=1).
        u_from_left = torch.roll(self.u, shifts=1, dims=0) * self.edge_left.unsqueeze(1)
        u_from_right = torch.roll(self.u, shifts=-1, dims=0) * self.edge_right.unsqueeze(1)
        
        # Apply strict ACI physical position coupling
        self.x = self.x + (self.MC2_LOCAL_RETAIN * self.u) + (neighbor_leak * u_from_left) + (neighbor_leak * u_from_right)
        
        # 5. Topological Damping & Stitching
        veto_mask = self.margin < 0.05
        
        if veto_mask.any():
            self.edge_left[veto_mask] = False
            self.edge_right[veto_mask] = False
            
            damped_x = self.synapse(self.x[veto_mask].unsqueeze(1)).squeeze(1)
            self.x[veto_mask] = damped_x
            
            self.u[veto_mask] *= 0.05
            self.p[veto_mask] *= 0.05
            
            norms = torch.norm(self.x, dim=1)
            dead_nodes = veto_mask & (norms < 1.0)
            
            if dead_nodes.any():
                self.x[dead_nodes] = 0.0
                self.p[dead_nodes] = 0.0
                self.edge_left[dead_nodes] = True
                self.edge_right[dead_nodes] = True
                
        return {
            "active_edges": self.edge_left.sum().item(),
            "mean_margin": self.margin.mean().item(),
            "lyapunov": self.calculate_lyapunov()
        }
