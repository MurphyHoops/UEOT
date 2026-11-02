# Reproduce the public source consumers

From the repository root, use the existing pinned Lean project (do not set a global default toolchain):

```sh
cd formalization/ueot-core
lake build UEOT
ueot_source_native="$PWD/docs/compression/theory_completion/unified_closure/general_perron_compact_spectral_source_v1/native_protocol"
ueot_source_out="$(mktemp -d /tmp/ueot-general-source.XXXXXX)"
ueot_source_path="$ueot_source_out:$(lake env printenv LEAN_PATH)"
lake env /usr/bin/env LEAN_PATH="$ueot_source_path" lean "$ueot_source_native/PUBLIC_PERRON_RETURNED_CERTIFICATE.lean"
for ueot_source_file in ueot-compact-killed-bool-kernel ueot-compact-killed-bool-fixture ueot-compact-killed-bool-common-consumer ueot-compact-killed-bool-operator-binding; do
  lake env /usr/bin/env LEAN_PATH="$ueot_source_path" lean -R "$ueot_source_native" -o "$ueot_source_out/$ueot_source_file.olean" "$ueot_source_native/$ueot_source_file.lean" || exit $?
done
```

All source bodies use the public UEOT entry; quoted helper imports are compiled in dependency order into the new temporary directory. The actual recorded validation uses an exclusive external output and excludes private author `/tmp` module imports. These checks construct the same returned Perron certificate and the same actual killed-kernel/L² consumers. They generate no empirical samples. Original A/C data certification is a separate official saved-data command against the final stable Core fingerprint.
