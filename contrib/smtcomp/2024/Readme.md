# Building the Bitwuzla Binary

To build the solver binary, use the following command:

```
docker build --output=. --target=bitwuzla_binary .
```

This will build and copy the Bitwuzla binary to directory `bin/` in the current
directory.
