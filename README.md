# IoTLogicChecker
The IoT-Logic Checker, a tool enabling automatic logic reasoning to identify logic weaknesses in RTE policy.

## Requirement
+ \*nix (tested under Linux, other platform may have bugs)
+ Python 3.6+
+ Twelf 1.7.1+ (modify *TWELF\_PATH* in config.py with the absolute path)

## Quick Start:
+ To find all bugs in one RTE policy:
```
python explore.py example_RTE_policy.txt
```

The result will be in *example\_RTE\_policy.txt.log*

+ To check one user action sequence in detail:
```
python check.py example_RTE_policy2.txt
firefox visualize/index.html
```

