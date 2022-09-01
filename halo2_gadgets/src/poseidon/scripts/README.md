# Poseidon hash parameters for 2 and 4 inputs

We use Daira code in order to generate parameters. It seems that it is a bit different from the code we used for ZK-Garage implementation (the round numbers for example).

## Round numbers

Using the command 
```python3
sage calc_round_numbers.py
```
we obtain the same values for `R_F` and `R_P`:
```
  t = 3
  M = 128
  alpha = 5
  security_margin = True
  R_F = 8
  R_P = 56
  min_sbox_cost = 80
  min_size_cost = 20320

============================================
  t = 5
  M = 128
  alpha = 5
  security_margin = True
  R_F = 8
  R_P = 56
  min_sbox_cost = 96
  min_size_cost = 24384

============================================
```
This is quite surprising and could be double-checked with Daira.

## Parameter grain

We generate the parameter grain from `R_F` and `R_P` plus extra parameters from the curve:
```python3
sage generate_parameters_grain.sage 1 0 255 3 8 56 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001 --rust
sage generate_parameters_grain.sage 1 0 255 5 8 56 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001 --rust
```
The values are added to `../fp.rs` so that we have the round numbers for Poseidon4 (and the numbers for Poseidon2 match :-)).

The same command is executed for `../fq.rs` with `0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001`.

## Test vectors

We generate the test vectors for `../p128pow5t3.rs` and `../p128pow5t5.rs` using the files `poseidonperm_x5_{curve}_{t}.sage` where `{curve}` is `pallas` and `vesta` and `{t}` is `3` and `5`.