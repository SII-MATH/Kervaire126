"""Keep the full KIPBase target complete without sweeping nested build caches."""
import os
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]


def configured_globs():
    config = (ROOT / 'lakefile.lean').read_text()
    block = config.split('lean_lib KIPBase where', 1)[1].split('\nlean_exe ', 1)[0]
    return re.findall(r'\.(one|submodules|andSubmodules)\s+`([A-Za-z0-9_.]+)', block)


def owned_modules():
    modules = {'KIPBase'}
    for directory, children, files in os.walk(ROOT / 'KIPBase'):
        children[:] = [name for name in children if not name.startswith('.')]
        for name in files:
            if name.endswith('.lean'):
                path = (Path(directory) / name).relative_to(ROOT).with_suffix('')
                modules.add('.'.join(path.parts))
    return modules


def selected(module, globs):
    return any(
        module == prefix if kind == 'one' else
        module.startswith(prefix + '.') or (kind == 'andSubmodules' and module == prefix)
        for kind, prefix in globs
    )


class KIPBaseBuildLayoutTests(unittest.TestCase):
    def test_all_owned_modules_are_selected(self):
        globs = configured_globs()
        self.assertTrue(globs, 'KIPBase needs an explicit build module inventory')
        missing = sorted(name for name in owned_modules() if not selected(name, globs))
        self.assertEqual(missing, [], 'Real project modules must not be excluded')

    def test_nested_cache_modules_are_not_selected(self):
        globs = configured_globs()
        for name in (
            'KIPBase..lake.packages.mathlib.Mathlib',
            'KIPBase..lake.packages.mathlib.Mathlib.AlgebraicGeometry.Scheme',
            'KIPBase..lake.packages.batteries.Batteries',
            'KIPBase..lake.build.ir.Generated',
        ):
            with self.subTest(module=name):
                self.assertFalse(selected(name, globs))


if __name__ == '__main__':
    unittest.main()
