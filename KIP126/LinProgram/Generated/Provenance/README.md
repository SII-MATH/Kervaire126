# Reconstruction records used by current replay

These four records supply fixed source reconstruction and native trace details
used by the current translators and the canonical `docs/external-inputs.json`
manifest. They are retained here because the formal repository excludes the
historical `docs/audits/` tree.

- `seed5487-next.json` records the original bounded resolution/secondary rebuild
  and the complete 96-row semantic fingerprint used by the seed generator.
- `naturality245131-chain-reconstruction.json` records the bounded Ceta chain
  rebuild used by the 21-degree batch.
- `naturality40-chain-reconstruction.json` records the corresponding 40-degree
  rebuild.
- `row462481-trace.json` is reconstructed from the fixed native archive and log by
  `Translate/extract-row462481-trace.py`; current archive and member paths point
  into `Source/LWXMachine/` and `Raw/`.

The three reconstruction records preserve their original bytes. Historical
paths, commands, timestamps and reported checks describe those original runs;
they are not current replay receipts or a second source registry. Historical
Lean module locators in the native trace are retained; the parent README maps
those declarations to their current modules. Current reconstruction checks use
the commands in `Translate/` and the pinned inputs in this checkout.

No recorded status establishes resolution exactness, an actual Adams
comparison, or a differential. Those mathematical obligations remain explicit
in the Lean interfaces and Blueprint.
