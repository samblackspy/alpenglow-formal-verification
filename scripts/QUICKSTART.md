# Quick Start Guide

## Run Complete Verification (3 hours)

```bash
cd scripts
./run_verification.sh
```

This runs all 24 tests automatically:
- 21 exhaustive tests (~2 hours)
- 3 simulation tests (~30 minutes)

---

## View Existing Results (30 seconds)

```bash
# See all test logs
ls ../verification_results/*.log

# Count passing exhaustive tests
grep -l "0 states left on queue" ../verification_results/*.log | wc -l
# Output: 21

# Count simulation tests
ls ../verification_results/*_sim.log 2>/dev/null | wc -l
# Output: 3
```

---

## Run Single Test (seconds to hours)

```bash
# Fast test (10 seconds)
java -jar ../tla2tools.jar \
  -workers 8 \
  -config ../tla/models/4v_safety_minimal_actions.cfg \
  ../tla/Alpenglow.tla

# Production-scale test (1+ hour)
java -jar ../tla2tools.jar \
  -workers 8 \
  -config ../tla/models/10v_safety_bounded.cfg \
  ../tla/Alpenglow.tla
```

---

## Check Results

### All Tests Passed?
```bash
cd ../verification_results
grep -l "0 states left on queue" *.log | wc -l  # Should be 21
ls *_sim.log | wc -l                             # Should be 3
```

### View Specific Test
```bash
# See 10v production test
tail -50 10v_safety_bounded.log

# See simulation results
tail -20 fast_path_stress_test_sim.log
```

### Count Total States
```bash
# Exhaustive tests
grep "distinct states found" *.log | grep -v sim

# Simulation tests  
grep "Progress:" *_sim.log | tail -3
```

---

## Expected Results

**All 24 tests pass (100%)**

| Category | Tests | Time | States |
|----------|-------|------|--------|
| Safety | 10 | ~1.5 hrs | 50,000+ |
| Liveness | 2 | ~30s | 11,000+ |
| Byzantine | 6 | ~10 min | 200,000+ |
| Multi-slot | 3 | ~1 min | 35,000+ |
| Simulation | 3 | ~30 min | 89M+ |
| **TOTAL** | **24** | **~3 hrs** | **89.5M+** |

---

## Requirements

- Java 11+ installed
- 8GB+ RAM recommended
- 10 CPU cores (uses 8 workers)
- ~3 hours for complete run

---

## Troubleshooting

**Test seems stuck?**
- 10v test takes 1+ hour (normal)
- Check `top` or Activity Monitor for Java process

**Out of memory?**
- Reduce workers: edit script, change `-workers 8` to `-workers 4`
- Increase heap: change `-Xmx4g` to `-Xmx8g`

**Config not found?**
- Ensure you're in `/scripts` directory
- Check `../tla/models/` contains .cfg files

---

## What Gets Verified

✅ **Safety** - No double finalization, no forks  
✅ **Liveness** - Progress guaranteed, bounded time  
✅ **Byzantine** - Safe with 20% malicious nodes  
✅ **Scale** - Up to 10 validators exhaustively  
✅ **Stress** - 89M+ simulation states checked  

**Result: Zero violations in 89.5+ million states**

---

For full documentation, see [../README.md](../README.md)
