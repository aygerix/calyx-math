"""
Plane curves
"""

# *****************************************************************************
#
#   Sage: Open Source Mathematical Software
#
#       Copyright (C) 2005 William Stein <was@math.harvard.edu>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#
#    This code is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
#    General Public License for more details.
#
#  The full text of the GPL is available at:
#
#                  https://www.gnu.org/licenses/
# *****************************************************************************

from sage.misc.lazy_import import lazy_import

from sage.schemes.curves.constructor import Curve
from sage.schemes.curves.projective_curve import Hasse_bounds

lazy_import('sage.schemes.curves.plane_curve_arrangement', 'PlaneCurveArrangements')

lazy_import('sage.schemes.curves.plane_curve_arrangement', 'AffinePlaneCurveArrangements')

lazy_import('sage.schemes.curves.plane_curve_arrangement', 'ProjectivePlaneCurveArrangements')

lazy_import(
    'sage.schemes.curves.coleman.data',
    ['ColemanIntegrationData', 'coleman_data', 'de_rham_cohomology_basis'],
)
lazy_import(
    'sage.schemes.curves.coleman.points',
    ['ColemanIntegrationPoint', 'ColemanTangentialPoint', 'tangential_point'],
)
lazy_import(
    'sage.schemes.curves.coleman.general_integration',
    'coleman_integrals_on_basis',
)
lazy_import(
    'sage.schemes.curves.coleman.integration',
    ['coleman_integral', 'coleman_integrals_on_basis_divisors'],
)
lazy_import(
    'sage.schemes.curves.coleman.chabauty',
    ['effective_chabauty', 'torsion_packet'],
)
