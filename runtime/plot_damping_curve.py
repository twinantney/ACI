import numpy as np

def generate_terminal_damping_visualization():
    print("==========================================================================")
    plt_title = "PHASE 43: MIDPOINT SHOCK & HEAVY FRICTION DAMPING DECAY TRAJECTORY"
    print(plt_title.center(74))
    print("==========================================================================")

    # Replicate the exact cross-sectional cycle coordinate data points
    cycles = [4995, 4996, 4997, 4998, 4999, 5000, 5001, 5002, 5003, 5004, 5005, 5006, 5007, 5008, 5009, 5010]
    margins = [
        -1.30, -1.30, -1.30, -1.30, -1.30, 
        -104878.77, 
        -123.12, -60.54, -28.91, -12.43, -7.17, -7.17, -7.17, -7.17, -7.17, -7.17
    ]

    # Map the massive symlog physical scale to a 20-row terminal display grid
    # Row indices map from top to bottom (0 = Near 0.05 Floor, 19 = Deep Negative Singularity)
    grid_width = len(cycles)
    grid_height = 20
    grid = [[" " for _ in range(grid_width)] for _ in range(grid_height)]

    for col_idx, val in enumerate(margins):
        if val == -104878.77:
            row_idx = 19  # Bottom of the grid (Absolute Impact Singularity Floor)
        elif val < -100:
            row_idx = 15  # Major suppression tier
        elif val < -50:
            row_idx = 10  # Intermediate recovery tier
        elif val < -20:
            row_idx = 6   # Accelerated damping zone
        elif val < -5:
            row_idx = 3   # Approaching stabilization plateau
        else:
            row_idx = 1   # High-level tracking baseline

        grid[row_idx][col_idx] = "*"

    # Render display grid with logarithmic scale markings on the Y-Axis
    scale_labels = [
        "   0.05 | ", "  -5.00 | ", " -12.00 | ", " -28.00 | ", 
        " -60.00 | ", " -123.1 | ", " -500.0 | ", "-104.8k | "
    ]
    label_map = {1: 0, 3: 1, 6: 2, 10: 3, 15: 5, 19: 7}

    for r in range(grid_height):
        axis_label = scale_labels[label_map[r]] if r in label_map else "        | "
        row_str = "".join(grid[r])
        # Replace the direct coordinate point with an unstyled path connector line for visibility
        row_str = row_str.replace(" ", " ")
        print(f"{axis_label}{row_str}")

    print("--------+-----------------------------------------------------------------")
    print(" Cycle:   95  96  97  98  99  00  01  02  03  04  05  06  07  08  09  10")
    print("          (Processing Cycles mapped relative to baseline milestone: 4900+)")
    print("==========================================================================")

if __name__ == "__main__":
    generate_terminal_damping_visualization()

