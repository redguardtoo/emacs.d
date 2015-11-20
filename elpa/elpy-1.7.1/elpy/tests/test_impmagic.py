# coding: utf-8

"""Tests for the elpy.impmagic module"""

import re
import unittest

from elpy import impmagic
from elpy.tests.support import BackendTestCase

TEST_SOURCE = '''# test file

import time
import logging

os.getcwd()
time.sleep(1)
'''


class ImportMagicTestCase(BackendTestCase):

    def setUp(self):
        if not impmagic.importmagic:
            raise unittest.SkipTest
        self.importmagic = impmagic.ImportMagic()
        super(ImportMagicTestCase, self).setUp()

    def build_index(self):
        self.project_file('mymod.py', 'class AnUncommonName:\n pass\n')
        self.importmagic.build_index(self.project_root,
                                     custom_path=[self.project_root],
                                     blacklist_re=re.compile('^$'))
        self.importmagic._thread.join()

    def test_get_symbols(self):
        self.build_index()
        candidates = self.importmagic.get_import_symbols('AnUncommonName')
        self.assertEqual(candidates, ['from mymod import AnUncommonName'])
        candidates = self.importmagic.get_import_symbols('mymod')
        self.assertEqual(candidates, ['import mymod'])

    def test_add_import(self):
        self.build_index()
        start, end, newblock = self.importmagic.add_import(
            TEST_SOURCE, 'from mymod import AnUncommonName')
        self.assertEqual(start, 2)
        self.assertEqual(end, 5)
        self.assertEqual(newblock.strip(),
                         'import logging\nimport time\n\nfrom mymod import AnUncommonName')

        start, end, newblock = self.importmagic.add_import(
            TEST_SOURCE, 'import mymod')
        self.assertEqual(start, 2)
        self.assertEqual(end, 5)
        self.assertEqual(newblock.strip(),
                         'import logging\nimport time\n\nimport mymod')

    def test_get_unresolved_symbols(self):
        self.build_index()
        symbols = self.importmagic.get_unresolved_symbols('x = a + b\ny = c.d')
        self.assertEqual(sorted(symbols), ['a', 'b', 'c.d'])

    def test_remove_unreferenced_imports(self):
        self.build_index()
        start, end, newblock = \
            self.importmagic.remove_unreferenced_imports(TEST_SOURCE)
        self.assertEqual(start, 2)
        self.assertEqual(end, 5)
        self.assertEqual(newblock.strip(), 'import time')
