# Contributing

There are two main components that Lampe tool contains:

* Lean's Lampe library that defines code used to create a proof.
* CLI tool written in Rust that generates Lampe's project structure and extracts Noir's code into Lean code.

## Testing

The project has few different level of tests.

### Rust tests

These are typical unit tests to check that our rust code works as expected.

To run rust tests you need to bump stack size. Use command:

```bash
RUST_MIN_STACK=16777216 cargo test
```

### E2E extraction tests

These are tests that check if extraction works, extracted code doesn't produce Lean errors and output is what we expect.

To run all tests simply run `./testing/test.sh` script. You can use help to find out other options:

```bash
> ./testing/test.sh -h
Usage: ./testing/test.sh
   [ -t | --test ] Name of directory with test to run
```

Example command to run single test `./testing/test.sh --test Multiple`.

#### Test structure

Each test is in its own directory and consists of single Noir's project (workspace). Test scripts also checks directory
for two special scripts to execute:

* clean.sh - this script is being run before running extraction. Its purpose is to manually remove some selected files.
* user_actions.sh - this script is being run after running extraction and before running Lean code. Its purpose is to
  simulate user operations on extracted project.

Example with both scripts being used can be found in `testing/MerkleFromScratch`.

For now, we do not yet defined flow for rerunning extraction on the project. Because of it if there are any intentional
changes that affects generated code committed generated output must be recreated. To do so just remove `lampe` directory
in each of test directory and rust test script. Then commit changes into the repo.

Helper command to remove all `lampe` directories:

```bash
find testing -mindepth 2 -maxdepth 2 | grep lampe | xargs rm -rf
```

### Noir's test

We periodically run extraction on testing examples that are used by Noir's developers in their repository
(https://github.com/noir-lang/noir/tree/master/test_programs). We are whitelisting directories that contains only tests
that are compiling for now. We do also have a list of tests (directories) that we expect to fail and success. If we
run a test that is not expected to fail or success it is treated as test failure.

To run tests you must provide local path to Noir's repository with `test_programs` directory.

```bash
./testing_noir/test.sh --noir-path "/home/user/noir"
```

You can also run single test with `--test` flag similar to E2E's testing script.

Full script help:

```bash
Usage: ./testing_noir/test.sh
   [ -t | --test  ] Name of directory (full path, ex. '/home/user/noir/noir_test_success/should_fail_with_matches') with test to run
   [ --noir-path  ] Path to noir repository
   [ --lampe-cmd  ] Lampe command (default: lampe)
   [ --lake-cmd   ] Lake command (default: lake)
   [ --log-dir    ] Path where to put logs (default: current directory)
   [ --log-stdout ] Define if logs should go to file or stdout - pass true (default: false)
```
