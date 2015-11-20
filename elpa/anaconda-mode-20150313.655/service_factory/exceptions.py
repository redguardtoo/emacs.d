"""
    service_factory.exceptions
    ~~~~~~~~~~~~~~~~~~~~~~~~~~

    This module contains exceptions raised by service factory.

    :copyright: (c) 2015 by Artem Malyshev.
    :license: GPL3, see LICENSE for more details.
"""

from __future__ import (
    absolute_import, unicode_literals, division, print_function)


class ServiceException(Exception):
    """Exception occurred in running service."""

    pass
