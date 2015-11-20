"""
    service_factory.validation
    ~~~~~~~~~~~~~~~~~~~~~~~~~~

    This module implement JSON-RPC request validation.

    :copyright: (c) 2015 by Artem Malyshev.
    :license: GPL3, see LICENSE for more details.
"""

from __future__ import (
    absolute_import, unicode_literals, division, print_function)

import six


def validate_version(request):
    """Validate request version."""

    correct_version = request['jsonrpc'] == '2.0'
    error = 'Incorrect version of the JSON-RPC protocol'
    assert correct_version, error


def validate_method(request):
    """Validate request method."""

    correct_method = isinstance(request['method'], six.string_types)
    error = 'Incorrect name of the method to be invoked'
    assert correct_method, error


def validate_params(request):
    """Validate request params."""

    if 'params' in request:
        correct_params = isinstance(request['params'], (list, dict))
        error = 'Incorrect parameter values'
        assert correct_params, error


def validate_id(request):
    """Validate request id."""

    if 'id' in request:
        correct_id = isinstance(
            request['id'],
            (six.string_types, int, None))
        error = 'Incorrect identifier'
        assert correct_id, error
