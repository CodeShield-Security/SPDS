/*******************************************************************************
 * Copyright (c) 2018 Fraunhofer IEM, Paderborn, Germany.
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * http://www.eclipse.org/legal/epl-2.0.
 *  
 * SPDX-License-Identifier: EPL-2.0
 *
 * Contributors:
 *     Johannes Spaeth - initial API and implementation
 *******************************************************************************/
package boomerang;

import boomerang.stats.IBoomerangStats;

public class BoomerangTimeoutException extends RuntimeException {

    private IBoomerangStats stats;
    private long elapsed;

    public BoomerangTimeoutException(long elapsed, IBoomerangStats stats) {
        this.elapsed = elapsed;
        this.stats = stats;
    }

    @Override
    public String toString() {
        return "Boomerang Timeout after " + elapsed + "ms\n " + stats;
    }
}
