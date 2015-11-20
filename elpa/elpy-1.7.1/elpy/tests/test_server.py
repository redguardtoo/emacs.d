# coding: utf-8

"""Tests for the elpy.server module"""

import os
import tempfile
import unittest

import mock

from elpy import rpc
from elpy import server
from elpy.tests import compat
from elpy.tests.support import BackendTestCase
import elpy.refactor


class ServerTestCase(unittest.TestCase):
    def setUp(self):
        self.srv = server.ElpyRPCServer()


class BackendCallTestCase(ServerTestCase):
    def assert_calls_backend(self, method):
        with mock.patch("elpy.server.get_source") as get_source:
            with mock.patch.object(self.srv, "backend") as backend:
                get_source.return_value = "transformed source"

                getattr(self.srv, method)("filename", "source", "offset")

                get_source.assert_called_with("source")
                getattr(backend, method).assert_called_with(
                    "filename", "transformed source", "offset"
                )


class TestInit(ServerTestCase):
    def test_should_not_select_a_backend_by_default(self):
        self.assertIsNone(self.srv.backend)


class TestRPCEcho(ServerTestCase):
    def test_should_return_arguments(self):
        self.assertEqual(("hello", "world"),
                         self.srv.rpc_echo("hello", "world"))


class TestRPCInit(ServerTestCase):
    @mock.patch("elpy.jedibackend.JediBackend")
    @mock.patch("elpy.ropebackend.RopeBackend")
    def test_should_set_project_root(self, RopeBackend, JediBackend):
        self.srv.rpc_init({"project_root": "/project/root",
                           "backend": "rope"})

        self.assertEqual("/project/root", self.srv.project_root)

    @mock.patch("elpy.jedibackend.JediBackend")
    @mock.patch("elpy.ropebackend.RopeBackend")
    def test_should_initialize_rope(self, RopeBackend, JediBackend):
        self.srv.rpc_init({"project_root": "/project/root",
                           "backend": "rope"})

        RopeBackend.assert_called_with("/project/root")

    @mock.patch("elpy.jedibackend.JediBackend")
    @mock.patch("elpy.ropebackend.RopeBackend")
    def test_should_initialize_jedi(self, RopeBackend, JediBackend):
        self.srv.rpc_init({"project_root": "/project/root",
                           "backend": "jedi"})

        JediBackend.assert_called_with("/project/root")

    @mock.patch("elpy.jedibackend.JediBackend")
    @mock.patch("elpy.ropebackend.RopeBackend")
    def test_should_use_rope_if_available_and_requested(
            self, RopeBackend, JediBackend):
        RopeBackend.return_value.name = "rope"
        JediBackend.return_value.name = "jedi"

        self.srv.rpc_init({"project_root": "/project/root",
                           "backend": "rope"})

        self.assertEqual("rope", self.srv.backend.name)

    @mock.patch("elpy.jedibackend.JediBackend")
    @mock.patch("elpy.ropebackend.RopeBackend")
    def test_should_use_jedi_if_available_and_requested(
            self, RopeBackend, JediBackend):
        RopeBackend.return_value.name = "rope"
        JediBackend.return_value.name = "jedi"

        self.srv.rpc_init({"project_root": "/project/root",
                           "backend": "jedi"})

        self.assertEqual("jedi", self.srv.backend.name)

    @mock.patch("elpy.jedibackend.JediBackend")
    @mock.patch("elpy.ropebackend.RopeBackend")
    def test_should_use_rope_if_available_and_nothing_requested(
            self, RopeBackend, JediBackend):
        RopeBackend.return_value.name = "rope"
        JediBackend.return_value.name = "jedi"

        self.srv.rpc_init({"project_root": "/project/root",
                           "backend": None})

        self.assertEqual("rope", self.srv.backend.name)

    @mock.patch("elpy.jedibackend.JediBackend")
    @mock.patch("elpy.ropebackend.RopeBackend")
    def test_should_use_jedi_if_rope_not_available_and_nothing_requested(
            self, RopeBackend, JediBackend):
        RopeBackend.return_value.name = "rope"
        JediBackend.return_value.name = "jedi"
        old_rope = server.ropebackend
        server.ropebackend = None

        try:
            self.srv.rpc_init({"project_root": "/project/root",
                               "backend": None})
        finally:
            server.ropebackend = old_rope

        self.assertEqual("jedi", self.srv.backend.name)

    @mock.patch("elpy.jedibackend.JediBackend")
    @mock.patch("elpy.ropebackend.RopeBackend")
    def test_should_use_none_if_nothing_available(
            self, RopeBackend, JediBackend):
        RopeBackend.return_value.name = "rope"
        JediBackend.return_value.name = "jedi"
        old_rope = server.ropebackend
        old_jedi = server.jedibackend
        server.ropebackend = None
        server.jedibackend = None

        try:
            self.srv.rpc_init({"project_root": "/project/root",
                               "backend": None})
        finally:
            server.ropebackend = old_rope
            server.jedibackend = old_jedi

        self.assertIsNone(self.srv.backend)


class TestRPCGetCalltip(BackendCallTestCase):
    def test_should_call_backend(self):
        self.assert_calls_backend("rpc_get_calltip")

    def test_should_handle_no_backend(self):
        self.srv.backend = None
        self.assertIsNone(self.srv.rpc_get_calltip("filname", "source",
                                                   "offset"))


class TestRPCGetCompletions(BackendCallTestCase):
    def test_should_call_backend(self):
        self.assert_calls_backend("rpc_get_completions")

    def test_should_handle_no_backend(self):
        self.srv.backend = None
        self.assertEqual([],
                         self.srv.rpc_get_completions("filname", "source",
                                                      "offset"))

    def test_should_sort_results(self):
        with mock.patch.object(self.srv, 'backend') as backend:
            backend.rpc_get_completions.return_value = [
                {'name': '_e'},
                {'name': '__d'},
                {'name': 'c'},
                {'name': 'B'},
                {'name': 'a'},
            ]
            expected = list(reversed(backend.rpc_get_completions.return_value))

            actual = self.srv.rpc_get_completions("filename", "source",
                                                  "offset")

            self.assertEqual(expected, actual)

    def test_should_uniquify_results(self):
        with mock.patch.object(self.srv, 'backend') as backend:
            backend.rpc_get_completions.return_value = [
                {'name': 'a'},
                {'name': 'a'},
            ]
            expected = [{'name': 'a'}]

            actual = self.srv.rpc_get_completions("filename", "source",
                                                  "offset")

            self.assertEqual(expected, actual)


class TestRPCGetCompletionDocs(ServerTestCase):
    def test_should_call_backend(self):
        with mock.patch.object(self.srv, "backend") as backend:
            self.srv.rpc_get_completion_docstring("completion")

            (backend.rpc_get_completion_docstring
             .assert_called_with("completion"))

    def test_should_handle_no_backend(self):
        self.srv.backend = None
        self.assertIsNone(self.srv.rpc_get_completion_docstring("foo"))


class TestRPCGetCompletionLocation(ServerTestCase):
    def test_should_call_backend(self):
        with mock.patch.object(self.srv, "backend") as backend:
            self.srv.rpc_get_completion_location("completion")

            (backend.rpc_get_completion_location
             .assert_called_with("completion"))

    def test_should_handle_no_backend(self):
        self.srv.backend = None
        self.assertIsNone(self.srv.rpc_get_completion_location("foo"))


class TestRPCGetDefinition(BackendCallTestCase):
    def test_should_call_backend(self):
        self.assert_calls_backend("rpc_get_definition")

    def test_should_handle_no_backend(self):
        self.srv.backend = None
        self.assertIsNone(self.srv.rpc_get_definition("filname", "source",
                                                      "offset"))


class TestRPCGetDocstring(BackendCallTestCase):
    def test_should_call_backend(self):
        self.assert_calls_backend("rpc_get_docstring")

    def test_should_handle_no_backend(self):
        self.srv.backend = None
        self.assertIsNone(self.srv.rpc_get_docstring("filname", "source",
                                                     "offset"))


class TestRPCGetPydocCompletions(ServerTestCase):
    @mock.patch.object(server, 'get_pydoc_completions')
    def test_should_call_pydoc_completions(self, get_pydoc_completions):
        srv = server.ElpyRPCServer()
        srv.rpc_get_pydoc_completions()
        get_pydoc_completions.assert_called_with(None)
        srv.rpc_get_pydoc_completions("foo")
        get_pydoc_completions.assert_called_with("foo")


class TestGetPydocDocumentation(ServerTestCase):
    @mock.patch("pydoc.render_doc")
    def test_should_find_documentation(self, render_doc):
        render_doc.return_value = "expected"

        actual = self.srv.rpc_get_pydoc_documentation("open")

        render_doc.assert_called_with("open",
                                      "Elpy Pydoc Documentation for %s",
                                      False)
        self.assertEqual("expected", actual)

    def test_should_return_none_for_unknown_module(self):
        actual = self.srv.rpc_get_pydoc_documentation("frob.open")

        self.assertIsNone(actual)

    def test_should_return_valid_unicode(self):
        import json

        docstring = self.srv.rpc_get_pydoc_documentation("tarfile")

        json.dumps(docstring)


class TestRPCGetRefactorOptions(BackendTestCase):
    @mock.patch.object(compat.builtins, '__import__')
    def test_should_fail_if_rope_is_not_available(self, import_):
        import_.side_effect = ImportError
        filename = self.project_file("foo.py", "")
        srv = server.ElpyRPCServer()
        self.assertRaises(ImportError, srv.rpc_get_refactor_options,
                          filename, 0)

    @mock.patch.object(elpy.refactor, 'Refactor')
    def test_should_initialize_and_call_refactor_object(self, Refactor):
        filename = self.project_file("foo.py", "import foo")
        srv = server.ElpyRPCServer()
        srv.project_root = self.project_root

        srv.rpc_get_refactor_options(filename, 5)

        Refactor.assert_called_with(self.project_root, filename)
        Refactor.return_value.get_refactor_options.assert_called_with(5, None)


class TestRPCRefactor(BackendTestCase):
    @mock.patch.object(compat.builtins, '__import__')
    def test_should_fail_if_rope_is_not_available(self, import_):
        import_.side_effect = ImportError
        filename = self.project_file("foo.py", "")
        srv = server.ElpyRPCServer()
        self.assertRaises(ImportError, srv.rpc_refactor,
                          filename, 'foo', ())

    @mock.patch.object(elpy.refactor, 'Refactor')
    def test_should_initialize_and_call_refactor_object_with_args(
            self, Refactor):
        filename = self.project_file("foo.py", "import foo")
        srv = server.ElpyRPCServer()
        srv.project_root = self.project_root

        srv.rpc_refactor(filename, 'foo', (1, 2, 3))

        Refactor.assert_called_with(self.project_root, filename)
        Refactor.return_value.get_changes.assert_called_with('foo', 1, 2, 3)

    @mock.patch.object(elpy.refactor, 'Refactor')
    def test_should_initialize_and_call_refactor_object_without_args(
            self, Refactor):
        filename = self.project_file("foo.py", "import foo")
        srv = server.ElpyRPCServer()
        srv.project_root = self.project_root

        srv.rpc_refactor(filename, 'foo', None)

        Refactor.assert_called_with(self.project_root, filename)
        Refactor.return_value.get_changes.assert_called_with('foo')


class TestRPCGetUsages(BackendCallTestCase):
    def test_should_call_backend(self):
        self.assert_calls_backend("rpc_get_usages")

    def test_should_handle_no_backend(self):
        self.srv.backend = None
        with self.assertRaises(rpc.Fault):
            self.assertIsNone(self.srv.rpc_get_usages("filname", "source",
                                                      "offset"))


class TestRPCImportMagic(ServerTestCase):
    def test_should_call_importmagic(self):
        with mock.patch.object(self.srv, "import_magic") as impmagic:
            self.srv.rpc_get_import_symbols("filename", "source", "os")
            impmagic.get_import_symbols.assert_called_with("os")
            self.srv.rpc_add_import("filename", "source", "import os")
            impmagic.add_import.assert_called_with("source", "import os")
            self.srv.rpc_get_unresolved_symbols("filename", "source")
            impmagic.get_unresolved_symbols.assert_called_with("source")
            self.srv.rpc_remove_unreferenced_imports("filename", "source")
            impmagic.remove_unreferenced_imports.assert_called_with("source")


class TestGetSource(unittest.TestCase):
    def test_should_return_string_by_default(self):
        self.assertEqual(server.get_source("foo"),
                         "foo")

    def test_should_return_file_contents(self):
        fd, filename = tempfile.mkstemp(prefix="elpy-test-")
        self.addCleanup(os.remove, filename)
        with open(filename, "w") as f:
            f.write("file contents")

        fileobj = {'filename': filename}

        self.assertEqual(server.get_source(fileobj),
                         "file contents")

    def test_should_clean_up_tempfile(self):
        fd, filename = tempfile.mkstemp(prefix="elpy-test-")
        with open(filename, "w") as f:
            f.write("file contents")

        fileobj = {'filename': filename,
                   'delete_after_use': True}

        self.assertEqual(server.get_source(fileobj),
                         "file contents")
        self.assertFalse(os.path.exists(filename))

    def test_should_support_utf8(self):
        fd, filename = tempfile.mkstemp(prefix="elpy-test-")
        self.addCleanup(os.remove, filename)
        with open(filename, "wb") as f:
            f.write(u"möp".encode("utf-8"))

        source = server.get_source({'filename': filename})

        self.assertEqual(source, u"möp")


class TestPysymbolKey(BackendTestCase):
    def keyLess(self, a, b):
        self.assertLess(b, a)
        self.assertLess(server._pysymbol_key(a),
                        server._pysymbol_key(b))

    def test_should_be_case_insensitive(self):
        self.keyLess("bar", "Foo")

    def test_should_sort_private_symbols_after_public_symbols(self):
        self.keyLess("foo", "_bar")

    def test_should_sort_private_symbols_after_dunder_symbols(self):
        self.assertLess(server._pysymbol_key("__foo__"),
                        server._pysymbol_key("_bar"))

    def test_should_sort_dunder_symbols_after_public_symbols(self):
        self.keyLess("bar", "__foo")
