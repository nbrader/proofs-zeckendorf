# zeckendorf_plot.py
# Generate Zeckendorf representation scatter plots and save as SVG files.

import matplotlib.pyplot as plt

def fib_up_to(max_n):
    """Return Fibonacci numbers up to max_n following Zeckendorf convention (1, 2, 3, 5, ...)."""
    fibs = [1, 2]
    while fibs[-1] + fibs[-2] <= max_n:
        fibs.append(fibs[-1] + fibs[-2])
    return fibs

def zeckendorf(n, fibs):
    """Return the Zeckendorf (greedy) decomposition of n."""
    components = []
    remaining = n
    for f in reversed(fibs):
        if f <= remaining:
            components.append(f)
            remaining -= f
    return components

def plot_zeckendorf(max_n, filename):
    """Generate and save the Zeckendorf scatter plot up to max_n."""
    fibs = fib_up_to(max_n)
    xs, ys = [], []

    for n in range(1, max_n + 1):
        comps = zeckendorf(n, fibs)
        for c in comps:
            xs.append(n)
            ys.append(c)

    plt.figure(figsize=(14, 6))
    plt.scatter(xs, ys, s=6)
    plt.xlabel('Number being represented (n)')
    plt.ylabel('Fibonacci component in Zeckendorf representation')
    plt.title(f'Zeckendorf components for integers 1 through {max_n}')
    plt.yticks(fibs)
    plt.ylim(0, max(fibs) + 10)
    plt.grid(axis='y', linestyle='--', linewidth=0.5)
    plt.tight_layout()
    plt.savefig(filename, format='svg')
    plt.close()
    print(f"Saved Zeckendorf plot for 1..{max_n} as '{filename}'")

if __name__ == "__main__":
    # Example usage:
    plot_zeckendorf(50, "zeckendorf_1_50.svg")
    plot_zeckendorf(1000, "zeckendorf_1_1000.svg")
