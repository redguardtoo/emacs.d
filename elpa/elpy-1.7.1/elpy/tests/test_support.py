"""Tests for elpy.tests.support. Yep, we test test code."""

import unittest

from elpy.tests.support import source_and_offset


class TestSourceAndOffset(unittest.TestCase):
    def test_should_return_source_and_offset(self):
        self.assertEqual(source_and_offset("hello, _|_world"),
                         ("hello, world", 7))

    def test_should_handle_beginning_of_string(self):
        self.assertEqual(source_and_offset("_|_hello, world"),
                         ("hello, world", 0))

    def test_should_handle_end_of_string(self):
        self.assertEqual(source_and_offset("hello, world_|_"),
                         ("hello, world", 12))
