#!/usr/bin/env python3
"""Print where the test time of a Maven build went.

Reads every surefire report (TEST-*.xml) under the given root (default: the
current directory) and prints the time per module and the slowest test
classes, so a CI log shows which tests make the build long.

Usage: scripts/test-times.py [root] [number of classes, default 60]
"""
import glob
import os
import sys
import xml.etree.ElementTree as ET


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else "."
    top = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    rows = []
    for path in glob.glob(os.path.join(root, "**/target/surefire-reports/TEST-*.xml"), recursive=True):
        module = os.path.relpath(path, root).split(os.sep)[0]
        try:
            suite = ET.parse(path).getroot()
        except ET.ParseError:
            continue
        name = suite.get("name", os.path.basename(path)).split(".")[-1]
        rows.append((float(suite.get("time", "0").replace(",", "")), module, name, int(suite.get("tests", "0"))))
    if not rows:
        print("no surefire reports found")
        return
    modules = {}
    for time, module, _, tests in rows:
        t, n, c = modules.get(module, (0.0, 0, 0))
        modules[module] = (t + time, n + tests, c + 1)
    total = sum(r[0] for r in rows)
    print(f"Test time: {total / 60:.1f} min in {len(rows)} classes")
    print(f"{'module':<24}{'min':>8}{'classes':>9}{'tests':>8}")
    for module, (t, n, c) in sorted(modules.items(), key=lambda kv: -kv[1][0]):
        print(f"{module:<24}{t / 60:>8.1f}{c:>9}{n:>8}")
    print(f"\nSlowest {top} test classes:")
    print(f"{'s':>8}{'tests':>7}  {'module':<20}class")
    for time, module, name, tests in sorted(rows, reverse=True)[:top]:
        print(f"{time:>8.1f}{tests:>7}  {module:<20}{name}")


if __name__ == "__main__":
    main()
