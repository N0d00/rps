#!/usr/bin/env python3
import os
import sys
import subprocess
import json
import random
import re

# Paths
REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CPP_PATH = os.path.join(REPO_ROOT, "engine", "rps_v4_engine.cpp")
WASM_PATH = os.path.join(REPO_ROOT, "rps_v4_engine.wasm")
WASI_CLANG = os.path.join(REPO_ROOT, "wasi-sdk", "bin", "clang++")
TOURNAMENT_SCRIPT = os.path.join(REPO_ROOT, "tools", "tournament.mjs")
RESULTS_JSON = os.path.join(REPO_ROOT, "tournament-results.json")

# Parameters to tune (Name: (Default Value, Step Size c_k, Type))
# We choose step sizes proportional to the scale of the parameter.
PARAMS = {
    "TERRITORY_W": {"val": 118.0, "step": 10.0},
    "PIECE_W": {"val": 760.0, "step": 100.0},
    "THREATENED_W": {"val": 165.0, "step": 20.0},
    "PREY_W": {"val": 82.0, "step": 10.0},
    "SAFE_NEUTRAL_W": {"val": 24.0, "step": 5.0},
    "NEUTRAL_W": {"val": 9.0, "step": 2.0},
    "MOBILITY_W": {"val": 3.0, "step": 1.0},
    "DIVERSITY_W": {"val": 42.0, "step": 8.0},
    "PROX_FAR_W": {"val": 22.0, "step": 5.0},
    "PROX_NEAR_W": {"val": 42.0, "step": 8.0},
    "LATE_TERR_W": {"val": 4.0, "step": 1.0},
}

# Hyperparameters for SPSA
A = 100  # Scaling for learning rate step decay
ALPHA = 0.602
GAMMA = 0.101

def compile_engine(param_values):
    # Read the template C++ file
    with open(CPP_PATH, "r") as f:
        content = f.read()

    # Replace values
    for name, val in param_values.items():
        # Find e.g., static const int TERRITORY_W = 118;
        pattern = r"(static\s+const\s+int\s+" + name + r"\s*=\s*)[-]?\d+;"
        replacement = rf"\g<1>{int(round(val))};"
        content, count = re.subn(pattern, replacement, content)
        if count == 0:
            print(f"Warning: could not replace parameter {name}")

    # Write back to temporary C++ file or keep in place
    temp_cpp = os.path.join(REPO_ROOT, "engine", "rps_v4_engine_tuner.cpp")
    with open(temp_cpp, "w") as f:
        f.write(content)

    # Compile using WASI SDK Clang
    cmd = [
        WASI_CLANG,
        "--target=wasm32-unknown-unknown",
        "-O3",
        "-fno-builtin",
        "-nostdlib",
        "-Wl,--no-entry",
        "-Wl,--export-memory",
        "-Wl,--allow-undefined",
        "-Wl,--initial-memory=16777216",
        "-Wl,--max-memory=134217728",
        temp_cpp,
        "-o",
        WASM_PATH
    ]
    
    res = subprocess.run(cmd, capture_output=True, text=True)
    if res.returncode != 0:
        print("Compilation failed!")
        print(res.stderr)
        sys.exit(1)

    # Clean up temp file
    if os.path.exists(temp_cpp):
        os.remove(temp_cpp)


def run_eval_tournament(games_per_pairing=20, time_ms=50):
    """
    Runs a tournament of rps-v4-engine vs rps-v2-1-engine.
    Returns the score (points) of rps-v4-engine.
    """
    if os.path.exists(RESULTS_JSON):
        os.remove(RESULTS_JSON)

    cmd = [
        "node",
        TOURNAMENT_SCRIPT,
        "--games-per-pairing", str(games_per_pairing),
        "--bots", "rps-v2-1-engine,rps-v4-engine",
        "--time-ms", str(time_ms)
    ]
    
    # Run the tournament
    subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

    if not os.path.exists(RESULTS_JSON):
        print("Tournament failed to produce results!")
        return 0.0

    with open(RESULTS_JSON, "r") as f:
        results = json.load(f)

    # Parse standings to find rps-v4-engine points
    v4_points = 0.0
    for standing in results.get("standings", []):
        if standing["bot"] == "rps-v4-engine":
            v4_points = standing["points"]
            break

    return v4_points


def spsa_tune(iterations=50, games_per_pairing=20, time_ms=50):
    theta = {name: data["val"] for name, data in PARAMS.items()}
    best_theta = dict(theta)
    best_score = -1.0

    # SPSA Coefficients Setup
    # Basic guidelines: a_k = a / (k + 1 + A)^alpha, c_k = c / (k + 1)^gamma
    # We calibrate a based on expected step size.
    a = 15.0  # Base learning rate multiplier

    print(f"Starting SPSA tuning for {iterations} iterations...")
    print(f"Initial parameters: {theta}")

    for k in range(iterations):
        # Step size decay
        ak = a / ((k + 1 + A) ** ALPHA)
        ck = 1.0 / ((k + 1) ** GAMMA)

        # Generate Bernoulli perturbation vector delta (+1 or -1)
        delta = {}
        theta_plus = {}
        theta_minus = {}

        for name, data in PARAMS.items():
            delta[name] = random.choice([-1.0, 1.0])
            step = data["step"] * ck
            theta_plus[name] = theta[name] + step * delta[name]
            theta_minus[name] = theta[name] - step * delta[name]

        # Evaluate theta_plus
        compile_engine(theta_plus)
        y_plus = run_eval_tournament(games_per_pairing, time_ms)

        # Evaluate theta_minus
        compile_engine(theta_minus)
        y_minus = run_eval_tournament(games_per_pairing, time_ms)

        # Gradient estimate
        # Since we want to MAXIMIZE points, gradient should point towards y_plus
        # g_k = (y_plus - y_minus) / (2 * c_k * delta)
        # Gradient descent: theta = theta + ak * g_k
        gradient = {}
        for name in PARAMS:
            c_k_step = PARAMS[name]["step"] * ck
            diff = y_plus - y_minus
            # To handle gradient step scaling:
            grad = (diff) / (2.0 * c_k_step * delta[name])
            gradient[name] = grad

        # Update parameters
        new_theta = {}
        for name in PARAMS:
            # We add because we are maximizing points
            new_theta[name] = theta[name] + ak * gradient[name] * PARAMS[name]["step"]
            # Keep bounds positive
            if new_theta[name] < 0:
                new_theta[name] = 0.0

        theta = new_theta

        print(f"Iteration {k+1}/{iterations}:")
        print(f"  y+ (theta+): {y_plus} pts | y- (theta-): {y_minus} pts")
        print(f"  Updated parameters: { {k: round(v, 2) for k, v in theta.items()} }")
        
        # Save best parameters
        current_avg_score = (y_plus + y_minus) / 2.0
        if current_avg_score > best_score:
            best_score = current_avg_score
            best_theta = dict(theta)

    print("\nTuning Complete!")
    print(f"Best parameters found (Avg Score vs baseline: {best_score} pts):")
    for name, val in best_theta.items():
        print(f"  {name} = {int(round(val))}")

    # Compile the final best engine
    compile_engine(best_theta)
    print("Compiled best parameters into rps_v4_engine.wasm")


if __name__ == "__main__":
    spsa_tune(iterations=10, games_per_pairing=20, time_ms=50)
