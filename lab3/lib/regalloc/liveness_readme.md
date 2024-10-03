## Required structures
- livein/liveout/uses/defs/movs/pred

1. Pre-processing:
  - Get the maximum number of lines
  - For each line:
    - Map string to int if it is a jump statement
    - Add the new variables to the table
        - To check for size
    - add the `defined` and `uses` to the tables (won't change when doing liveness)

2. Build predecessor table
  - For each line `l`:
    - If it is conditional jump to `ljump`:
      - Get line of `ljump`
      - `ljump.add(curr_line)`
      - `lnext.add(curr_line)`
    - If it is jump to `ljump`:
      - Get line of `ljump`
      - `ljump.add(curr_line)`
    - Otherwise:
      - `lnext.add(curr_line)`

3. Work backwards, for each line:
  - For each variable that it uses:
    - if it is in live-in, skip
    - else:
      - add to live-in
      - run `4`

4. Work on current variable:
  - For each predecessor:
    - if variable is live-out
      - assert that variable is either live-in or defined
      - (Since you only add to live-out when running the algorithm)
    - if variable is not live-out
      - add to live-out
      - check if it is defined
        - if defined, stop
      - if not defined, add to live-in
        - run `4`