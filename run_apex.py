#!/usr/bin/env python3
import sys
sys.path.append("/home/phil/.gemini/antigravity/scratch/BioNPC/src")
sys.path.append("./src")
import argparse
import time
import json
import logging
from apex_tensor import ApexMasterTensorRuntime

def main():
    parser = argparse.ArgumentParser(description="Run Production ACI Tensor Engine")
    parser.add_argument("--nodes", type=int, default=100000, help="Number of nodes to simulate")
    parser.add_argument("--steps", type=int, default=1500, help="Total simulation steps")
    parser.add_argument("--device", type=str, default=None, help="Device (cuda or cpu)")
    parser.add_argument("--output", type=str, default="production_intelligence_metrics.json")
    args = parser.parse_args()

    logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
    logger = logging.getLogger("ApexRunner")

    logger.info(f"Initializing ACI GPU Engine (BioNPC Enabled) with {args.nodes:,} nodes...")
    rt = ApexMasterTensorRuntime(node_count=args.nodes, device=args.device)

    telemetry = []
    logger.info(f"Starting {args.steps} execution cycles...")
    
    t0 = time.time()
    for s in range(1, args.steps + 1):
        metrics = rt.step(s)
        
        if s % 100 == 0 or s == 1:
            logger.info(f"Cycle {s:04d} | Edges: {metrics['active_edges']:,} | Margin: {metrics['mean_margin']:.4f} | Lyapunov: {metrics['lyapunov']:.2e}")
            telemetry.append({
                "iteration": s,
                "metrics": metrics
            })
            
    tf = time.time() - t0
    
    logger.info("Simulation Complete.")
    logger.info(f"Execution Time: {tf:.3f}s | Throughput: {args.steps/tf:.1f} FPS")

    # Generate ACI Production Payload
    report = {
        "timestamp": time.time(),
        "hardware": rt.device,
        "nodes_processed": args.nodes,
        "total_steps": args.steps,
        "execution_time_seconds": tf,
        "fps": args.steps / tf,
        "final_lyapunov_divergence": metrics['lyapunov'],
        "evolution_history": telemetry
    }
    
    with open(args.output, "w") as f:
        json.dump(report, f, indent=2)
        
    logger.info(f"Data archived to {args.output}")

if __name__ == "__main__":
    main()
