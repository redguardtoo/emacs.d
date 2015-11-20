import os
import unittest
import shutil
import sys
import tempfile

import mock

import elpy.pydocutils


class TestGetPydocCompletions(unittest.TestCase):
    def test_should_return_top_level_modules(self):
        modules = elpy.pydocutils.get_pydoc_completions("")
        self.assertIn('sys', modules)
        self.assertIn('json', modules)
        self.assertIn('elpy', modules)

    def test_should_return_submodules(self):
        modules = elpy.pydocutils.get_pydoc_completions("elpy")
        self.assertIn("elpy.rpc", modules)
        self.assertIn("elpy.server", modules)
        modules = elpy.pydocutils.get_pydoc_completions("os")
        self.assertIn("os.path", modules)

    def test_should_find_objects_in_module(self):
        self.assertIn("elpy.tests.test_pydocutils.TestGetPydocCompletions",
                      elpy.pydocutils.get_pydoc_completions
                      ("elpy.tests.test_pydocutils"))

    def test_should_find_attributes_of_objects(self):
        attribs = elpy.pydocutils.get_pydoc_completions(
            "elpy.tests.test_pydocutils.TestGetPydocCompletions")
        self.assertIn("elpy.tests.test_pydocutils.TestGetPydocCompletions."
                      "test_should_find_attributes_of_objects",
                      attribs)

    def test_should_return_none_for_inexisting_module(self):
        self.assertEqual([],
                         elpy.pydocutils.get_pydoc_completions
                         ("does_not_exist"))

    def test_should_work_for_unicode_strings(self):
        self.assertIsNotNone(elpy.pydocutils.get_pydoc_completions
                             (u"sys"))

    def test_should_find_partial_completions(self):
        self.assertIn("multiprocessing",
                      elpy.pydocutils.get_pydoc_completions
                      ("multiprocess"))
        self.assertIn("multiprocessing.util",
                      elpy.pydocutils.get_pydoc_completions
                      ("multiprocessing.ut"))

    def test_should_ignore_trailing_dot(self):
        self.assertIn("elpy.pydocutils",
                      elpy.pydocutils.get_pydoc_completions
                      ("elpy."))


class TestGetModules(unittest.TestCase):
    def test_should_return_top_level_modules(self):
        modules = elpy.pydocutils.get_modules()
        self.assertIn('sys', modules)
        self.assertIn('json', modules)
        self.assertIn('elpy', modules)

    def test_should_return_submodules(self):
        modules = elpy.pydocutils.get_modules("elpy")
        self.assertIn("rpc", modules)
        self.assertIn("server", modules)

    @mock.patch.object(elpy.pydocutils, 'safeimport')
    def test_should_catch_import_errors(self, safeimport):
        def raise_function(message):
            raise elpy.pydocutils.ErrorDuringImport(message,
                                                    (None, None, None))
        safeimport.side_effect = raise_function
        self.assertEqual([], elpy.pydocutils.get_modules("foo.bar"))

    def test_should_not_fail_for_permission_denied(self):
        tmpdir = tempfile.mkdtemp(prefix="test-elpy-get-modules-")
        sys.path.append(tmpdir)
        os.chmod(tmpdir, 0o000)
        try:
            elpy.pydocutils.get_modules()
        finally:
            os.chmod(tmpdir, 0o755)
            shutil.rmtree(tmpdir)
            sys.path.remove(tmpdir)
