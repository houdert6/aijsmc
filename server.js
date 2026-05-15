const WebSocket = require('ws');
const fs = require('fs');
const { spawn } = require('child_process');

const disableVersionCheck = process.argv.includes('--novercheck');
const SERVER_VERSION = '1.9.2';

const wss = new WebSocket.Server({host: '0.0.0.0', port: 25565 });

// --- SERVER WORLD STATE ---
// players: id -> {id, x, y, z, dim, username, mode, health, maxHealth, inventory: { type: count }, lastDamageTime: 0}
const players = new Map(); 
const mobs = [];
// worldBlocks: "x,y,z,dim" -> { type: string, state: object }
const worldBlocks = new Map(); 
const villagePOIs = []; // Store interesting locations {x, y, z, type}
const projectiles = []; // { id, x, y, z, vx, vy, vz, dim, ownerId, life }
const spawners = []; // { x, y, z, dim, timer, mobType }
let hostId = null;

// Anomaly State Tracking
let hostHTMLSnapshot = null;
let pendingSessions = new Map(); // sessionId -> Saved Player Data
let hostSessionId = null;

// Timing & Day/Night Cycle
let prevTime = performance.now();
let worldTime = 0;
const DAY_DURATION = 600; // Seconds for a full day/night cycle

// TPS Tracking
let currentTPS = 20.0;
let ticksThisSecond = 0;
let lastTpsTime = performance.now();
let lastTickDuration = 0;

// Config
const WORLD_SIZE = 40;
const BLOCK_SIZE = 5;

// Helper
const getKey = (x, y, z, dim) => Math.round(x) + ',' + Math.round(y) + ',' + Math.round(z) + ',' + dim;

// Fluid Queue
const fluidQueue = new Set(); // Stores keys "x,y,z,dim" of blocks to update

function base32tohex(base32) {
    let base32chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567";
    let bits = "";
    let hex = "";
    for (let i = 0; i < base32.length; i++) {
        let val = base32chars.indexOf(base32.charAt(i).toUpperCase());
        if (val === -1) throw new Error("Invalid base32");
        bits += val.toString(2).padStart(5, '0');
    }
    for (let i = 0; i+4 <= bits.length; i+=4) {
        let chunk = bits.substr(i, 4);
        hex += parseInt(chunk, 2).toString(16);
    }
    return hex;
}

function getTOTP(secret, window = 0) {
    try {
        const crypto = require('crypto');
        let key = Buffer.from(base32tohex(secret), 'hex');
        let epoch = Math.floor(Date.now() / 1000);
        let time = Buffer.alloc(8);
        time.writeUInt32BE(Math.floor(epoch / 30) + window, 4);
        let hmac = crypto.createHmac('sha1', key).update(time).digest();
        let offset = hmac[hmac.length - 1] & 0xf;
        let otp = (
            ((hmac[offset] & 0x7f) << 24) |
            ((hmac[offset + 1] & 0xff) << 16) |
            ((hmac[offset + 2] & 0xff) << 8) |
            (hmac[offset + 3] & 0xff)
        ) % 1000000;
        return otp.toString().padStart(6, '0');
    } catch(e) { return null; }
}

function verifyTOTP(secret, token) {
    return getTOTP(secret, 0) === token || getTOTP(secret, -1) === token || getTOTP(secret, 1) === token;
}

function generateBase32Secret() {
    const chars = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ234567';
    let secret = '';
    for(let i=0; i<16; i++) secret += chars[Math.floor(Math.random() * chars.length)];
    return secret;
}

// Unbreakable blocks in Survival
const UNBREAKABLE_BLOCKS = ['bedrock', 'end_frame', 'end_frame_filled', 'portal', 'nether_portal', 'network_block', '2fa_block', 'wool_chest', 'dark_brick'];

// --- TRADING CONFIG ---
const TRADE_POOL = {
    buys: [ 
        { costItem: 'dirt', costCount: 12, rewardItem: 'emerald', rewardCount: 1 },
        { costItem: 'sand', costCount: 12, rewardItem: 'emerald', rewardCount: 1 },
        { costItem: 'wood', costCount: 8, rewardItem: 'emerald', rewardCount: 1 },
        { costItem: 'stone', costCount: 16, rewardItem: 'emerald', rewardCount: 1 },
        { costItem: 'cactus', costCount: 6, rewardItem: 'emerald', rewardCount: 2 },
        // --- NEW: COLD BIOME TRADES (High Value) ---
        { costItem: 'snow_block', costCount: 4, rewardItem: 'emerald', rewardCount: 1 }, 
        { costItem: 'packed_ice', costCount: 2, rewardItem: 'emerald', rewardCount: 1 } 
    ],
    sells: [ 
        // ... existing sell trades ...
        { costItem: 'emerald', costCount: 1, rewardItem: 'wood', rewardCount: 6 },
        { costItem: 'emerald', costCount: 3, rewardItem: 'obsidian', rewardCount: 2 },
        { costItem: 'emerald', costCount: 5, rewardItem: 'eye_of_ender', rewardCount: 1 },
        { costItem: 'emerald', costCount: 8, rewardItem: 'end_frame', rewardCount: 1 },
        { costItem: 'emerald', costCount: 2, rewardItem: 'end_stone', rewardCount: 4 }
    ]
};

function generateVillagerTrades() {
    const trades = [];
    // Pick 3 random Buy trades
    for(let i=0; i<3; i++) {
        trades.push(TRADE_POOL.buys[Math.floor(Math.random() * TRADE_POOL.buys.length)]);
    }
    // Pick 2 random Sell trades
    for(let i=0; i<2; i++) {
        trades.push(TRADE_POOL.sells[Math.floor(Math.random() * TRADE_POOL.sells.length)]);
    }
    return trades;
}

// --- WORLD GENERATION ---
function simpleNoise(x, z) { return Math.abs(Math.sin(x*0.1) + Math.cos(z*0.1)) * 2; }

function generateSulfurCave(dim) {
    const cx = 0;
    const cy = -105 * BLOCK_SIZE; // Directly beneath the Abyss floor
    const cz = 0;
    const radius = 15;

    for (let x = -radius; x <= radius; x++) {
        for (let y = -radius; y <= radius; y++) {
            for (let z = -radius; z <= radius; z++) {
                const dist = Math.sqrt(x*x + y*y + z*z);
                if (dist > radius) continue;
                
                const wx = cx + x * BLOCK_SIZE;
                const wy = cy + y * BLOCK_SIZE;
                const wz = cz + z * BLOCK_SIZE;
                
                if (dist > radius - 2) {
                    addBlock(wx, wy, wz, 'cinnabar', dim);
                } else if (y < -radius + 4) {
                    if (Math.random() < 0.1) addBlock(wx, wy, wz, 'potent_sulfur', dim);
                    else addBlock(wx, wy, wz, 'sulfur_block', dim);
                } else {
                    const k = getKey(wx, wy, wz, dim);
                    if (worldBlocks.has(k)) worldBlocks.delete(k);
                }
            }
        }
    }
}

function generateAbyss(dim) {
    const bottomY = -80; // Sink deep into the world
    for (let y = 2; y >= bottomY; y--) {
        for (let x = -20; x <= 20; x++) {
            for (let z = -20; z <= 20; z++) {
                const dist = Math.sqrt(x*x + z*z);
                if (dist > 20) continue;

                const blockX = x * BLOCK_SIZE;
                const blockY = y * BLOCK_SIZE;
                const blockZ = z * BLOCK_SIZE;

                // Massive outer cylindrical cave wall
                if (dist >= 18) {
                    if (Math.random() > 0.1) addBlock(blockX, blockY, blockZ, 'stone', dim);
                    else if (Math.random() > 0.95) addBlock(blockX, blockY, blockZ, 'glowstone', dim);
                } else {
                    if (y === bottomY) {
                        // Bottom floor: Safe water landing in center, lava everywhere else
                        if (dist < 5) addBlock(blockX, blockY, blockZ, 'water', dim, {level: 8});
                        else if (dist < 17) addBlock(blockX, blockY, blockZ, 'lava', dim);
                    } else if (y < -5 && y > bottomY) {
                        // Sweeping spiral staircase into the deep
                        const angle = Math.atan2(z, x);
                        const spiral = (y * 0.3) % (Math.PI * 2);
                        let diff = Math.abs(angle - spiral);
                        if (diff > Math.PI) diff = Math.PI * 2 - diff;
                        
                        if (diff < 0.6 && dist > 5) {
                            addBlock(blockX, blockY, blockZ, 'stone', dim);
                            if (Math.random() < 0.2) addBlock(blockX, blockY - BLOCK_SIZE, blockZ, 'stone', dim);
                            if (Math.random() < 0.05) addBlock(blockX, blockY + BLOCK_SIZE, blockZ, 'red_mushroom', dim);
                        }
                    }
                }
            }
        }
    }
    const altarY = Math.floor(bottomY / 2) * BLOCK_SIZE;
    addBlock(0, altarY - BLOCK_SIZE, 0, 'stone', dim);
    addBlock(0, altarY, 0, 'wool_chest', dim);
}

function generateSkyIslandsServer(dim) {
    const cx = 20000;
    const cz = 20000;
    const cy = 120 * BLOCK_SIZE; 
    
    buildIslandServer(cx, cy, cz, 16, dim, true);
    buildIslandServer(cx + 40 * BLOCK_SIZE, cy + 6 * BLOCK_SIZE, cz + 10 * BLOCK_SIZE, 12, dim, false);
    buildSuspensionBridgeServer(cx + 12*BLOCK_SIZE, cy + BLOCK_SIZE, cz, cx + 30*BLOCK_SIZE, cy + 7*BLOCK_SIZE, cz + 8*BLOCK_SIZE, dim);
}

function buildIslandServer(x, y, z, r, dim, isPicnic) {
    for(let dx = -r; dx <= r; dx++) {
        for(let dy = -r; dy <= 2; dy++) {
            for(let dz = -r; dz <= r; dz++) {
                const dist = Math.sqrt(dx*dx + dy*dy + dz*dz);
                if (dist > r) continue;
                if (dy > 0 && Math.random() > 0.4) continue;
                
                const wx = x + dx*BLOCK_SIZE; const wy = y + dy*BLOCK_SIZE; const wz = z + dz*BLOCK_SIZE;
                
                if (dy === 0 || dy === 1 || dy === 2) {
                    if (isPicnic && dx > -5 && dx < 5 && dz > -5 && dz < 5) {
                        if (dy === 0) addBlock(wx, wy, wz, 'sand', dim);
                        else if (dy === 1) {
                            addBlock(wx, wy, wz, 'water', dim, {level: 8});
                            if (dx === 0 && dz === 0) addBlock(wx, wy+BLOCK_SIZE, wz, 'lily_pad', dim, { isSkyLift: true });
                            else if (Math.random() < 0.15) addBlock(wx, wy+BLOCK_SIZE, wz, 'lily_pad', dim);
                        }
                    } else {
                        if (!worldBlocks.has(getKey(wx, wy, wz, dim))) {
                            addBlock(wx, wy, wz, 'grass', dim);
                            if (Math.random() < 0.08) addBlock(wx, wy+BLOCK_SIZE, wz, Math.random() > 0.5 ? 'flower_pink' : 'flower_white', dim);
                            else if (Math.random() < 0.02 && dist > 5) buildCustomTreeServer(wx, wy+BLOCK_SIZE, wz, dim, Math.random() > 0.4 ? 'cherry_leaves' : 'leaves');
                        }
                    }
                } else if (dy === -1 || dy === -2) { addBlock(wx, wy, wz, 'dirt', dim); } 
                else { addBlock(wx, wy, wz, 'stone', dim); }
                
                if (dy === -Math.floor(r) && Math.random() < 0.15) {
                    const len = Math.floor(Math.random() * 6) + 2;
                    for(let v = 1; v <= len; v++) addBlock(wx, wy - v*BLOCK_SIZE, wz, 'vine', dim);
                }
            }
        }
    }
    if (isPicnic) {
        for(let cx = 6; cx <= 9; cx++) {
            for(let cz = 6; cz <= 9; cz++) { addBlock(x + cx*BLOCK_SIZE, y + BLOCK_SIZE, z + cz*BLOCK_SIZE, 'red_carpet', dim); }
        }
        addBlock(x - 6*BLOCK_SIZE, y + BLOCK_SIZE, z, 'wood', dim);
        addBlock(x - 6*BLOCK_SIZE, y + 2*BLOCK_SIZE, z, 'wood', dim);
        addBlock(x - 6*BLOCK_SIZE, y + 3*BLOCK_SIZE, z, 'wood', dim);
        addBlock(x - 5*BLOCK_SIZE, y + 2*BLOCK_SIZE, z, 'void_sign', dim, { text: "The Void Sea\nI am here\n-Tork" });
        buildCustomTreeServer(x - 6*BLOCK_SIZE, y + 4*BLOCK_SIZE, z, dim, 'cherry_leaves', 3);
        
        spawnMob('tork', x - 4*BLOCK_SIZE, y + 1.5*BLOCK_SIZE, z, dim);
    }
}

function generateFrostedTaigaServer(dim) {
    const offset = -300;
    const size = 180;
    
    // Phase 1: Solid Terrain
    for (let x = 0; x < size; x++) {
        for (let z = -size/2; z < size/2; z++) {
            const worldX = (x + offset) * BLOCK_SIZE;
            const worldZ = z * BLOCK_SIZE;

            const h = Math.sin(x * 0.05) * 2 + Math.cos(z * 0.05) * 2;
            const yHeight = Math.floor(h);

            addBlock(worldX, yHeight * BLOCK_SIZE, worldZ, 'snow_block', dim);
            addBlock(worldX, (yHeight - 1) * BLOCK_SIZE, worldZ, 'dirt', dim);
            
            for (let dy = yHeight - 2; dy >= -20; dy--) {
                addBlock(worldX, dy * BLOCK_SIZE, worldZ, 'stone', dim);
            }
            addBlock(worldX, -21 * BLOCK_SIZE, worldZ, 'obsidian', dim);
        }
    }
    
    // Phase 2: Procedural Cave Carvers (Worms)
    const numWorms = 40; 
    for(let w = 0; w < numWorms; w++) {
        let cx = (Math.random() * size + offset) * BLOCK_SIZE;
        let cz = (Math.random() * size - size/2) * BLOCK_SIZE;
        let cy = (Math.random() * 15 - 5) * BLOCK_SIZE; 
        
        let yaw = Math.random() * Math.PI * 2;
        let pitch = (Math.random() - 0.5) * 0.8;
        let radius = 1.5 + Math.random() * 2.5; 
        const length = 40 + Math.random() * 80; 
        
        for(let i = 0; i < length; i++) {
            const rInt = Math.ceil(radius);
            for(let dx = -rInt; dx <= rInt; dx++) {
                for(let dy = -rInt; dy <= rInt; dy++) {
                    for(let dz = -rInt; dz <= rInt; dz++) {
                        if (dx*dx + dy*dy + dz*dz <= radius*radius) {
                            const bx = Math.round((cx + dx*BLOCK_SIZE)/BLOCK_SIZE)*BLOCK_SIZE;
                            const by = Math.round((cy + dy*BLOCK_SIZE)/BLOCK_SIZE)*BLOCK_SIZE;
                            const bz = Math.round((cz + dz*BLOCK_SIZE)/BLOCK_SIZE)*BLOCK_SIZE;
                            
                            const k = getKey(bx, by, bz, dim);
                            if (worldBlocks.has(k)) {
                                const b = worldBlocks.get(k);
                                if (b.type !== 'obsidian') worldBlocks.delete(k);
                            }
                        }
                    }
                }
            }
            
            cx += Math.cos(yaw) * Math.cos(pitch) * BLOCK_SIZE;
            cy += Math.sin(pitch) * BLOCK_SIZE;
            cz += Math.sin(yaw) * Math.cos(pitch) * BLOCK_SIZE;
            
            yaw += (Math.random() - 0.5) * 0.8;
            pitch += (Math.random() - 0.5) * 0.6;
            if (pitch > 0.8) pitch = 0.8;
            if (pitch < -0.9) pitch = -0.9; 
            
            radius += (Math.random() - 0.5) * 0.5;
            if (radius < 1.5) radius = 1.5;
            if (radius > 4.5) radius = 4.5;
        }
    }
    
    // Phase 3: Surface Trees & Shrines
    for (let x = 0; x < size; x++) {
        for (let z = -size/2; z < size/2; z++) {
            const worldX = (x + offset) * BLOCK_SIZE;
            const worldZ = z * BLOCK_SIZE;
            const h = Math.sin(x * 0.05) * 2 + Math.cos(z * 0.05) * 2;
            const yHeight = Math.floor(h);

            const k = getKey(worldX, yHeight * BLOCK_SIZE, worldZ, dim);
            if (worldBlocks.has(k) && Math.random() > 0.96) {
                buildTaigaTreeServer(worldX, (yHeight + 1) * BLOCK_SIZE, worldZ, dim);
            }
            
            if (Math.random() < 0.0003) {
                const shrineY = (-15 + Math.floor(Math.random() * 10)) * BLOCK_SIZE;
                buildIceShrineServer(worldX, shrineY, worldZ, dim);
            }
            
            for (let dy = yHeight - 2; dy >= -20; dy--) {
                const k = getKey(worldX, dy * BLOCK_SIZE, worldZ, dim);
                const b = worldBlocks.get(k);
                if (b && b.type === 'stone') {
                    const upK = getKey(worldX, (dy+1)*BLOCK_SIZE, worldZ, dim);
                    const upM = worldBlocks.get(upK);
                    const isExposed = !upM || upM.type === 'air';
                    const chance = isExposed ? 0.08 : 0.005;
                    if (Math.random() < chance) {
                        worldBlocks.delete(k);
                        addBlock(worldX, dy * BLOCK_SIZE, worldZ, 'ice_shard', dim);
                    }
                }
            }
        }
    }
}

function buildIceShrineServer(x, y, z, dim) {
    for (let dx = -3; dx <= 3; dx++) {
        for (let dy = -1; dy <= 4; dy++) {
            for (let dz = -3; dz <= 3; dz++) {
                const wx = x + dx * BLOCK_SIZE; 
                const wy = y + dy * BLOCK_SIZE; 
                const wz = z + dz * BLOCK_SIZE;
                
                const k = getKey(wx, wy, wz, dim);
                if (worldBlocks.has(k)) worldBlocks.delete(k);
                
                if (Math.abs(dx) < 3 && Math.abs(dz) < 3 && dy > -1 && dy < 4) continue; 
                const isCorner = Math.abs(dx) === 3 && Math.abs(dz) === 3;
                addBlock(wx, wy, wz, isCorner ? 'packed_ice' : 'cobblestone', dim);
            }
        }
    }
    addBlock(x, y, z, 'frozen_chest', dim);
    addBlock(x, y, z + 2*BLOCK_SIZE, 'spawner', dim, { type: 'frostbound' });
    spawners.push({ x: x, y: y, z: z + 2*BLOCK_SIZE, dim: dim, timer: 0, mobType: 'frostbound' });
    if (Math.random() > 0.5) addBlock(x - 2*BLOCK_SIZE, y + 2*BLOCK_SIZE, z, 'lantern', dim);
}

function buildTaigaTreeServer(x, y, z, dim) {
    const height = 5 + Math.floor(Math.random() * 3);
    for(let i=0; i<height; i++) addBlock(x, y + i*BLOCK_SIZE, z, 'wood', dim);
    
    for(let ly = 1; ly < height + 2; ly++) {
        const radius = Math.max(0, Math.floor((height - ly) / 2) + 1);
        if (radius === 0 && ly < height + 1) continue;
        for(let lx = -radius; lx <= radius; lx++) {
            for(let lz = -radius; lz <= radius; lz++) {
                if (lx === 0 && lz === 0 && ly < height) continue; 
                if (Math.abs(lx) === radius && Math.abs(lz) === radius && radius > 1 && Math.random() > 0.5) continue; 
                addBlock(x + lx*BLOCK_SIZE, y + ly*BLOCK_SIZE, z + lz*BLOCK_SIZE, 'leaves', dim);
            }
        }
    }
}

function buildCustomTreeServer(x, y, z, dim, leafType, radius=2) {
    for(let i=0; i<4; i++) addBlock(x, y + (i*BLOCK_SIZE), z, 'wood', dim);
    const topY = y + (4*BLOCK_SIZE);
    for(let lx=-radius; lx<=radius; lx++) {
        for(let lz=-radius; lz<=radius; lz++) {
            for(let ly=0; ly<=1; ly++) {
                if(Math.abs(lx)===radius && Math.abs(lz)===radius) continue; 
                if(lx===0 && lz===0 && ly===0) continue;
                addBlock(x + (lx*BLOCK_SIZE), topY + (ly*BLOCK_SIZE), z + (lz*BLOCK_SIZE), leafType, dim);
            }
        }
    }
    addBlock(x, topY + (2*BLOCK_SIZE), z, leafType, dim);
}

function buildSuspensionBridgeServer(x1, y1, z1, x2, y2, z2, dim) {
    const dx = x2 - x1; const dy = y2 - y1; const dz = z2 - z1;
    const dist = Math.sqrt(dx*dx + dz*dz); 
    const steps = Math.floor(dist / BLOCK_SIZE);
    
    for (let i = 0; i <= steps; i++) {
        const t = i / steps;
        const px = Math.round((x1 + dx * t) / BLOCK_SIZE) * BLOCK_SIZE;
        const pz = Math.round((z1 + dz * t) / BLOCK_SIZE) * BLOCK_SIZE;
        const droop = Math.sin(t * Math.PI) * 3 * BLOCK_SIZE;
        const py = Math.round((y1 + dy * t - droop) / BLOCK_SIZE) * BLOCK_SIZE;
        
        const pathBlock = i % 2 === 0 ? 'wooden_slab' : 'wood';
        addBlock(px, py, pz, pathBlock, dim);
        addBlock(px + BLOCK_SIZE, py, pz, pathBlock, dim);
        addBlock(px - BLOCK_SIZE, py, pz, pathBlock, dim);
        
        if (i % 3 === 0) {
            addBlock(px + 2*BLOCK_SIZE, py + BLOCK_SIZE, pz, 'fence', dim);
            addBlock(px - 2*BLOCK_SIZE, py + BLOCK_SIZE, pz, 'fence', dim);
            if (Math.random() < 0.4) addBlock(px + 2*BLOCK_SIZE, py + 2*BLOCK_SIZE, pz, 'lantern', dim);
        }
        if (Math.random() < 0.25) {
            const len = Math.floor(Math.random() * 4) + 1;
            for (let c = 1; c <= len; c++) addBlock(px + BLOCK_SIZE, py - c*BLOCK_SIZE, pz, Math.random() > 0.5 ? 'chain' : 'vine', dim);
            if (Math.random() < 0.3) addBlock(px + BLOCK_SIZE, py - (len+1)*BLOCK_SIZE, pz, 'lantern', dim);
        }
    }
}

function generateOverworld() {
    for (let x = -WORLD_SIZE/2; x < WORLD_SIZE/2; x++) {
        for (let z = -WORLD_SIZE/2; z < WORLD_SIZE/2; z++) {
            const distToCenter = Math.sqrt(x*x + z*z);
            if (distToCenter < 7) continue; // Punch a massive hole in the center of the map

            const xp = x * BLOCK_SIZE;
            const zp = z * BLOCK_SIZE;
            const yHeight = Math.floor(simpleNoise(x, z));
            addBlock(xp, yHeight * BLOCK_SIZE, zp, 'grass', 'overworld');
            for(let d=1; d<=2; d++) addBlock(xp, (yHeight - d) * BLOCK_SIZE, zp, 'dirt', 'overworld');
            
            if (x > -10 && x < 10 && z > -10 && z < 10) { 
                if (Math.random() > 0.96) createTree(xp, (yHeight + 1) * BLOCK_SIZE, zp, 'overworld');
            }

            if (Math.random() < 0.02) {
                const type = Math.random() > 0.6 ? 'zombie' : 'villager';
                spawnMob(type, xp, (yHeight + 2) * BLOCK_SIZE, zp, 'overworld');
            }
        }
    }
    generateAbyss('overworld');
    generateSulfurCave('overworld');
    generateDesert();
    generateLake('overworld');
    generateIceSpikesBiome();
}

function generateDesert() {
    const offset = 30; 
    const size = 60;
    for (let x = 0; x < size; x++) {
        for (let z = -size/2; z < size/2; z++) {
            const worldX = (x + offset) * BLOCK_SIZE;
            const worldZ = z * BLOCK_SIZE;
            const h = Math.sin(x * 0.1) * 1.5 + Math.cos(z * 0.1) * 1.5;
            const yHeight = Math.floor(h);
            addBlock(worldX, yHeight * BLOCK_SIZE, worldZ, 'sand', 'overworld');
            addBlock(worldX, (yHeight - 1) * BLOCK_SIZE, worldZ, 'sand', 'overworld');
            addBlock(worldX, (yHeight - 2) * BLOCK_SIZE, worldZ, 'stone', 'overworld');
            if (Math.random() > 0.99) {
                const ch = Math.floor(Math.random() * 2) + 2; 
                for(let cy=1; cy<=ch; cy++) addBlock(worldX, (yHeight + cy) * BLOCK_SIZE, worldZ, 'cactus', 'overworld');
            }
        }
    }
    generateVillage((offset + size/2) * BLOCK_SIZE, 0 * BLOCK_SIZE);
}

function generateIgloo(cx, cy, cz, dim) {
    // Dome
    for(let dx=-2; dx<=2; dx++) {
        for(let dz=-2; dz<=2; dz++) {
            for(let dy=0; dy<=3; dy++) {
                const wx = cx + dx*BLOCK_SIZE; const wy = cy + dy*BLOCK_SIZE; const wz = cz + dz*BLOCK_SIZE;
                if (dy === 3 && (Math.abs(dx)===2 || Math.abs(dz)===2)) continue;
                if (dy > 0 && dy < 3 && Math.abs(dx) < 2 && Math.abs(dz) < 2) continue;
                if (dy > 0 && dy < 3 && dx === 2 && dz === 0) continue; 
                
                const k = getKey(wx, wy, wz, dim);
                if (worldBlocks.has(k)) worldBlocks.delete(k);
                addBlock(wx, wy, wz, 'snow_block', dim);
            }
        }
    }

    // Shaft
    for(let dy=0; dy>=-12; dy--) {
        const wy = cy + dy*BLOCK_SIZE;
        const k = getKey(cx, wy, cz, dim);
        if (worldBlocks.has(k)) worldBlocks.delete(k);
    }

    // Permafrost Labyrinth Generation
    const by = cy - 12*BLOCK_SIZE;
    const mazeSize = 15;
    const grid = [];
    for(let x=0; x<mazeSize; x++) { grid[x] = []; for(let z=0; z<mazeSize; z++) grid[x][z] = 1; }
    
    const stack = [[7, 7]]; grid[7][7] = 0; // Shaft landing at center
    grid[7][6] = 0; stack.push([7, 6]); // Force a path out of the landing
    while(stack.length > 0) {
        const [mx, mz] = stack[stack.length - 1];
        const dirs = [[0,-2],[0,2],[-2,0],[2,0]].sort(() => Math.random()-0.5);
        let carved = false;
        for(let d of dirs) {
            const nx = mx + d[0]; const nz = mz + d[1];
            if(nx>0 && nx<mazeSize-1 && nz>0 && nz<mazeSize-1 && grid[nx][nz] === 1) {
                grid[mx + d[0]/2][mz + d[1]/2] = 0; 
                grid[nx][nz] = 0;
                stack.push([nx, nz]); carved = true; break;
            }
        }
        if(!carved) stack.pop();
    }

    // Build Maze
    for(let x=0; x<mazeSize; x++) {
        for(let z=0; z<mazeSize; z++) {
            const wx = cx + (x - 7) * BLOCK_SIZE;
            const wz = cz + (z - 7) * BLOCK_SIZE;
            
            for(let dy=0; dy<=3; dy++) {
                const k = getKey(wx, by + dy*BLOCK_SIZE, wz, dim);
                if (worldBlocks.has(k)) worldBlocks.delete(k);
            }

            if (x === 7 && z === 7) addBlock(wx, by - BLOCK_SIZE, wz, '2fa_block', dim);
            else addBlock(wx, by - BLOCK_SIZE, wz, 'snow_block', dim);
            addBlock(wx, by + 4*BLOCK_SIZE, wz, 'stone', dim);

            if (grid[x][z] === 1) {
                for(let dy=0; dy<=3; dy++) addBlock(wx, by + dy*BLOCK_SIZE, wz, 'packed_ice', dim);
            } else {
                if (x === 7 && z === 7) {
                    addBlock(wx, by, wz, 'water', dim, {level: 8});
                } else if (x === 7 && z === 6) {
                    addBlock(wx, by, wz, 'mysterious_door', dim, { open: false });
                } else {
                    let neighbors = 0;
                    if(x>0) neighbors += grid[x-1][z];
                    if(x<mazeSize-1) neighbors += grid[x+1][z];
                    if(z>0) neighbors += grid[x][z-1];
                    if(z<mazeSize-1) neighbors += grid[x][z+1];
                    
                    if (neighbors >= 3) {
                        if (Math.random() < 0.4) {
                            addBlock(wx, by, wz, 'frozen_chest', dim);
                        } else if (Math.random() < 0.5) {
                            spawnMob('frostbound', wx, by, wz, dim);
                        }
                    } else if (Math.random() < 0.05) {
                        spawnMob('frostbound', wx, by, wz, dim);
                    }
                }
            }
        }
    }
}

function generateIceSpikesBiome() {
    const offset = -100; // Moved further away (was -40)
    const size = 60;
    let iglooGenerated = false;
    
    for (let x = 0; x < size; x++) {
        for (let z = -size/2; z < size/2; z++) {
            const worldX = (x + offset) * BLOCK_SIZE;
            const worldZ = z * BLOCK_SIZE;
            
            // Smoother, flatter terrain for ice plains
            const h = Math.abs(Math.sin(x * 0.05) + Math.cos(z * 0.05)); 
            const yHeight = Math.floor(h);

            // Ground: Snow Block on top, Dirt below
            addBlock(worldX, yHeight * BLOCK_SIZE, worldZ, 'snow_block', 'overworld');
            addBlock(worldX, (yHeight - 1) * BLOCK_SIZE, worldZ, 'dirt', 'overworld');
            addBlock(worldX, (yHeight - 2) * BLOCK_SIZE, worldZ, 'stone', 'overworld');

            // Ice Spikes & Igloo Generation
            if (Math.random() > 0.985) {
                if (!iglooGenerated && Math.random() > 0.8) {
                    generateIgloo(worldX, yHeight * BLOCK_SIZE, worldZ, 'overworld');
                    iglooGenerated = true;
                } else {
                const height = 10 + Math.floor(Math.random() * 15); // Tall spikes
                const isThick = Math.random() > 0.7; // 30% chance for thick spike

                for (let i = 1; i <= height; i++) {
                    const py = (yHeight + i) * BLOCK_SIZE;
                    
                    // Thin Spike
                    addBlock(worldX, py, worldZ, 'packed_ice', 'overworld');
                    
                    // Thick Spike Base (Tapers off near top)
                    if (isThick && i < height * 0.7) {
                        addBlock(worldX + BLOCK_SIZE, py, worldZ, 'packed_ice', 'overworld');
                        addBlock(worldX, py, worldZ + BLOCK_SIZE, 'packed_ice', 'overworld');
                        addBlock(worldX + BLOCK_SIZE, py, worldZ + BLOCK_SIZE, 'packed_ice', 'overworld');
                        }
                    }
                }
            }
        }
    }
}

// --- RANDOMIZED VILLAGE GENERATION ---
function generateVillage(cx, cz) {
    const dim = 'overworld';
    const villageY = 2 * BLOCK_SIZE; 
    
    // REDUCED Street Length to ensure it stays inside the generated Desert biome
    const streetLength = 25;
    
    for(let z = -streetLength; z <= streetLength; z+=BLOCK_SIZE) {
        for(let x = -5; x <= 5; x+=BLOCK_SIZE) {
             addBlock(cx + x, villageY, cz + z, 'stone', dim);
        }
    }
    
    const step = 20; 
    // Constrain loop to new street length
    let farmGenerated = false;
    for(let z = -streetLength + 10; z <= streetLength - 10; z += step) {
        // Left Side
        if (Math.random() > 0.3 || !farmGenerated) { 
            const type = (Math.random() > 0.7 || !farmGenerated) ? 'farm' : 'house'; 
            if (type === 'farm') farmGenerated = true; 
            const px = cx - 15 * BLOCK_SIZE;
            const pz = cz + z * BLOCK_SIZE;
            
            if (type === 'house') {
                buildHouse(px, villageY + BLOCK_SIZE, pz, dim);
                villagePOIs.push({ x: px, y: villageY + BLOCK_SIZE, z: pz, type: 'house' });
            } else {
                buildFarm(px - 10*BLOCK_SIZE, villageY, pz, dim);
                villagePOIs.push({ x: px, y: villageY + BLOCK_SIZE, z: pz, type: 'farm' });
            }
        }

        // Right Side
        if (Math.random() > 0.3) {
            const type = Math.random() > 0.7 ? 'farm' : 'house';
            const px = cx + 15 * BLOCK_SIZE;
            const pz = cz + z * BLOCK_SIZE;
            
            if (type === 'house') {
                buildHouse(px, villageY + BLOCK_SIZE, pz, dim);
                villagePOIs.push({ x: px, y: villageY + BLOCK_SIZE, z: pz, type: 'house' });
            } else {
                buildFarm(px + 10*BLOCK_SIZE, villageY, pz, dim);
                villagePOIs.push({ x: px, y: villageY + BLOCK_SIZE, z: pz, type: 'farm' });
            }
        }
    }
    
    // Secret Pedestals for the Market Quest (Placed after buildings to prevent overwriting)
    addBlock(cx + 15, villageY, cz + 15, 'snow_block', dim);
    addBlock(cx - 15, villageY, cz + 15, 'netherrack', dim);
    addBlock(cx, villageY, cz - 15, 'obsidian', dim);

    // Spawn villagers closer to center
    const count = 5 + Math.floor(Math.random() * 8);
    global.villageInitialCap = count;
    for(let i=0; i<count; i++) {
        // Tighter spawn radius
        const vx = cx + (Math.random() - 0.5) * 20 * BLOCK_SIZE;
        const vz = cz + (Math.random() - 0.5) * 40 * BLOCK_SIZE;
        // Handle Server vs Client spawn syntax
        if (typeof spawnMob === 'function') {
            // Client
            if (typeof isConnected !== 'undefined') {
                 // index.html version
                 spawnMob(vx, villageY + 5 * BLOCK_SIZE, vz, 'villager', dim, 'clientMob');
            } else {
                 // server.js version
                 spawnMob('villager', vx, villageY + 5 * BLOCK_SIZE, vz, dim);
            }
        }
    }
}

function buildHouse(x, y, z, dim) {
    for(let i=0; i<5; i++) {
        for(let k=0; k<5; k++) {
            const bx = x + (i-2)*BLOCK_SIZE;
            const bz = z + (k-2)*BLOCK_SIZE;
            
            // Foundation Logic
            for(let fy = y - BLOCK_SIZE; fy > -50; fy -= BLOCK_SIZE) {
                const kKey = getKey(bx, fy, bz, dim);
                if (worldBlocks.has(kKey)) break;
                addBlock(bx, fy, bz, 'stone', dim);
            }

            for(let j=0; j<4; j++) {
                const by = y + j*BLOCK_SIZE;
                if (i===0 || i===4 || k===0 || k===4 || j===0) {
                    if (j===0) addBlock(bx, by, bz, 'stone', dim);
                    else {
                        // Door Logic: Front wall (k==0), center (i==2), height 0 & 1
                        if (i===2 && k===0 && j < 2) {
                            // Default door state: closed
                            addBlock(bx, by, bz, 'door', dim, { open: false });
                            continue;
                        }
                        
                        if (j < 3 && i===2 && k===0) continue;
                        if (j===2 && (i===0 || i===4 || k===4)) { continue; }
                        addBlock(bx, by, bz, 'sand', dim);
                    }
                }
            }
            const topY = y + 4*BLOCK_SIZE;
            addBlock(bx, topY, bz, 'wood', dim);
        }
    }
}

function buildFarm(x, y, z, dim) {
    for(let i=0; i<7; i++) {
        for(let k=0; k<7; k++) {
            const bx = x + (i-3)*BLOCK_SIZE;
            const bz = z + (k-3)*BLOCK_SIZE;
            
            // Foundation Logic
            for(let fy = y - BLOCK_SIZE; fy > -50; fy -= BLOCK_SIZE) {
                const kKey = getKey(bx, fy, bz, dim);
                if (worldBlocks.has(kKey)) break;
                addBlock(bx, fy, bz, 'stone', dim);
            }

            if (i===0 || i===6 || k===0 || k===6) {
                addBlock(bx, y+BLOCK_SIZE, bz, 'wood', dim);
            } else {
                if (i===3) {
                    addBlock(bx, y, bz, 'water', dim);
                } else {
                    addBlock(bx, y, bz, 'dirt', dim);
                    addBlock(bx, y+BLOCK_SIZE, bz, 'crop', dim);
                }
            }
        }
    }
}

function generateNether() {
    const size = 40;
    const dim = 'the_nether';
    
    // Generate Terrain
    for (let x = -size; x < size; x++) {
        for (let z = -size; z < size; z++) {
            const xp = x * BLOCK_SIZE; const zp = z * BLOCK_SIZE;
            addBlock(xp, 30*BLOCK_SIZE, zp, 'bedrock', dim);
            const h = Math.floor(Math.abs(Math.sin(x*0.1) + Math.cos(z*0.1)) * 2);
            for(let y=0; y<=h; y++) {
                let type = 'netherrack';
                if (Math.random() < 0.05) type = 'quartz_ore';
                addBlock(xp, y*BLOCK_SIZE, zp, type, dim);
            }

            // Magma & Lava
            if (h < 2) {
                addBlock(xp, 2*BLOCK_SIZE, zp, 'lava', dim);
            }
            
            // Surface Magma Patches
            if (Math.random() < 0.03) {
                addBlock(xp, h*BLOCK_SIZE, zp, 'magma', dim);
            }

            if (Math.random() < 0.02) addBlock(xp, 28*BLOCK_SIZE, zp, 'glowstone', dim);
            if (h > 2 && Math.random() < 0.03) addBlock(xp, (h+1)*BLOCK_SIZE, zp, 'red_mushroom', dim);
            
            // Pigmen
            if (Math.random() < 0.01 && h > 2) {
                 spawnMob('pigman', xp, (h+1)*BLOCK_SIZE, zp, dim);
            }
        }
    }

    // Generate Blaze Citadels
    // We'll place 4 citadels at cardinal directions
    const citadelOffsets = [
        {x: 20, z: 20}, {x: -20, z: -20}, {x: 20, z: -20}, {x: -20, z: 20}
    ];

    citadelOffsets.forEach(offset => {
        generateCitadel(offset.x * BLOCK_SIZE, 10 * BLOCK_SIZE, offset.z * BLOCK_SIZE, dim);
    });
}

function generateDesertMarketServer(dim) {
    const cx = 50000;
    const cz = 50000;
    const size = 25;
    let mercatorCount = 0;
    
    const layout = [];
    for(let x=0; x<=size*2; x++) {
        layout[x] = [];
        for(let z=0; z<=size*2; z++) {
            if (x % 6 < 2 || z % 6 < 2) layout[x][z] = 1;
            else layout[x][z] = 0;
            if (layout[x][z] === 1 && Math.random() < 0.08) layout[x][z] = 0;
        }
    }

    for(let x = -size; x <= size; x++) {
        for(let z = -size; z <= size; z++) {
            const gridX = x + size;
            const gridZ = z + size;
            const isPath = layout[gridX][gridZ] === 1;
            
            const wx = cx + x * BLOCK_SIZE;
            const wz = cz + z * BLOCK_SIZE;

            addBlock(wx, 0, wz, isPath ? 'cobblestone' : 'sandstone', dim);
            addBlock(wx, -BLOCK_SIZE, wz, 'sandstone', dim);

            if (isPath) {
                if (Math.random() < 0.85) addBlock(wx, 12 * BLOCK_SIZE, wz, 'stick_roof', dim);
                if (Math.random() < 0.02) addBlock(wx, 7 * BLOCK_SIZE, wz, 'market_sign', dim);
            } else {
                let adjPath = false;
                if (gridX > 0 && layout[gridX-1][gridZ] === 1) adjPath = true;
                if (gridX < size*2 && layout[gridX+1][gridZ] === 1) adjPath = true;
                if (gridZ > 0 && layout[gridX][gridZ-1] === 1) adjPath = true;
                if (gridZ < size*2 && layout[gridX][gridZ+1] === 1) adjPath = true;

                if (adjPath) {
                    addBlock(wx, BLOCK_SIZE, wz, 'wood', dim);
                    
                    if (Math.random() < 0.25) {
                        let mobType = 'merchant';
                        if (mercatorCount < 4 && (Math.random() < 0.1 || mercatorCount === 0)) {
                            mobType = 'mercator';
                            mercatorCount++;
                        }
                        spawnMob(mobType, wx, 1.5 * BLOCK_SIZE, wz, dim);
                    } else {
                        const displays = ['market_carpet_1', 'market_carpet_2', 'wood', 'sandstone', 'leaves', 'cactus'];
                        const disp = displays[Math.floor(Math.random() * displays.length)];
                        addBlock(wx, 2 * BLOCK_SIZE, wz, disp, dim);
                    }

                    addBlock(wx, 4 * BLOCK_SIZE, wz, 'market_awning', dim);
                    for(let y = 5; y <= 14; y++) {
                        addBlock(wx, y * BLOCK_SIZE, wz, 'sandstone', dim);
                    }
                } else {
                    for(let y = 1; y <= 14; y++) {
                        addBlock(wx, y * BLOCK_SIZE, wz, 'sandstone', dim);
                    }
                }
            }
        }
    }
}

function generateDarkWorldServer() {
    const dim = 'dark_world';

    // Cyber Field Generate (80000, 80000)
    const cyX = 80000; const cyZ = 80000;
    for(let i=0; i<60; i++) {
        for(let w=-8; w<=8; w++) {
            addBlock(cyX + w*BLOCK_SIZE, 0, cyZ + i*BLOCK_SIZE, 'cyber_floor', dim);
            addBlock(cyX + w*BLOCK_SIZE, -BLOCK_SIZE, cyZ + i*BLOCK_SIZE, 'cyber_wire', dim);
        }
        if (i%10 === 0) {
            for(let h=1; h<10+Math.random()*15; h++) {
                addBlock(cyX - 20*BLOCK_SIZE, h*BLOCK_SIZE, cyZ + i*BLOCK_SIZE, 'cyber_building', dim);
                addBlock(cyX + 20*BLOCK_SIZE, h*BLOCK_SIZE, cyZ + i*BLOCK_SIZE, 'cyber_building', dim);
            }
        }
    }
    
    spawnMob('scc', cyX, 5, cyZ + 5*BLOCK_SIZE, dim);
    
    // Queen and Berdly encounter
    const q = spawnMob('queen', cyX, 5, cyZ + 25*BLOCK_SIZE, dim);
    q.queenEncounter = true;
    spawnMob('berdly', cyX + 10, 5, cyZ + 25*BLOCK_SIZE, dim);

    const length = 120; // Massive winding road
    for (let i = 0; i <= length; i++) {
        const cx = i * BLOCK_SIZE;
        const rawCz = Math.sin(i * 0.1) * 20 * BLOCK_SIZE; // Sine wave winding
        const cz = Math.round(rawCz / BLOCK_SIZE) * BLOCK_SIZE; // Fixed grid offset
        const radius = 6 + (i > length - 20 ? 15 : 0); // Widen into a massive clearing for the castle
        
        let chestPlaced = false;

        for (let dx = -radius; dx <= radius; dx++) {
            for (let dz = -radius; dz <= radius; dz++) {
                if (dx*dx + dz*dz <= radius*radius) {
                    // Ground
                    addBlock(cx + dx*BLOCK_SIZE, 0, cz + dz*BLOCK_SIZE, 'dark_grass', dim);
                    
                    // Starry Trees along the edges
                    if (i < length - 20 && Math.random() < 0.03 && dx*dx + dz*dz > (radius-2)*(radius-2)) {
                        for(let ty=1; ty<=6; ty++) addBlock(cx + dx*BLOCK_SIZE, ty*BLOCK_SIZE, cz + dz*BLOCK_SIZE, 'dark_tree_log', dim);
                        for(let ly=4; ly<=8; ly++) {
                            for(let lx=-2; lx<=2; lx++) {
                                for(let lz=-2; lz<=2; lz++) {
                                    if (Math.abs(lx)===2 && Math.abs(lz)===2) continue;
                                    addBlock(cx + (dx+lx)*BLOCK_SIZE, ly*BLOCK_SIZE, cz + (dz+lz)*BLOCK_SIZE, 'dark_tree_leaves', dim);
                                }
                            }
                        }
                    }
                    
                    // Guaranteed spaced chests along the edges
                    if (i > 0 && i % 25 === 0 && i < length - 20 && !chestPlaced) {
                        if (dx*dx + dz*dz > (radius-2)*(radius-2)) {
                            addBlock(cx + dx*BLOCK_SIZE, BLOCK_SIZE, cz + dz*BLOCK_SIZE, 'deltarune_chest', dim);
                            chestPlaced = true;
                        }
                    }
                    
                    // The Dark Castle (End of the road)
                    if (i > length - 20) {
                        // The Great Door Wall (1 block thick)
                        if (i === length - 15 && dx === 0 && Math.abs(dz) <= radius) {
                            for(let cy=1; cy<=10; cy++) {
                                const bx = cx + dx*BLOCK_SIZE; const by = cy*BLOCK_SIZE; const bz = cz + dz*BLOCK_SIZE;
                                addBlock(bx, by, bz, 'dark_brick', dim, { isGreatDoor: true });
                            }
                        }
                        
                        // Castle Walls (Perimeter only)
                        if (i >= length - 15) {
                            if (Math.abs(dz) === radius || (i === length && dx === radius)) {
                                for(let cy=1; cy<=15; cy++) {
                                    const bx = cx + dx*BLOCK_SIZE; const by = cy*BLOCK_SIZE; const bz = cz + dz*BLOCK_SIZE;
                                    addBlock(bx, by, bz, 'dark_brick', dim);
                                }
                            }
                        }
                        
                        // Ralsei outside the door
                        if (i === length - 16 && dx === 0 && dz === 0) {
                            spawnMob('ralsei', cx, 5, cz, dim);
                        }
                        
                        // Lancer inside the boss room
                        if (i === length - 5 && dx === 0 && dz === 0) {
                            const l = spawnMob('lancer', cx, 5, cz, dim);
                            l.lancerEncounter = true;
                        }
                    }
                }
            }
        }
    }
}

// --- DELTARUNE BATTLE SYSTEM ---
function sendBattleState(player, mob, stateOverride = null) {
    if (!mob.battle) return;
    const pRalsei = mobs.find(m => m.type === 'ralsei' && m.inParty && m.ownerId === player.id);
    const pOwca = mobs.find(m => m.type === 'owca' && m.ownerId === player.id);
    
    const client = getClientById(player.id);
    if (client) {
        client.send(JSON.stringify({
            type: 'battle_state',
            state: stateOverride || mob.battle.state,
            mobId: mob.id,
            playerHp: player.health,
            ralseiHp: pRalsei ? pRalsei.health : 0,
            owcaHp: pOwca ? pOwca.health : 0,
            hasRalsei: !!pRalsei,
            hasOwca: !!pOwca
        }));
    }
}

function startDeltaruneBattle(mob, player) {
    mob.battle = {
        active: true,
        playerId: player.id,
        state: 'menu',
        timer: 0,
        vulnerable: false,
        tired: false
    };
    player.battleId = mob.id;
    const partyOwca = mobs.find(m => m.type === 'owca' && m.ownerId === player.id);
    if (partyOwca) {
        const client = getClientById(player.id);
        if (client) client.send(JSON.stringify({ type: 'deltarune_text', text: ['* You watch owca play deltarune. He plays the game for you.' ]}));
        mob.health = 0;
        endDeltaruneBattle(mob);
        return;
    }
    sendBattleState(player, mob, 'menu');
}

function endDeltaruneBattle(mob) {
    if (!mob.battle) return;
    const player = players.get(mob.battle.playerId);
    if (player) player.battleId = null;
    const client = getClientById(mob.battle.playerId);
    if (client) client.send(JSON.stringify({ type: 'battle_state', state: 'ended' }));
    mob.battle.active = false;
    
    if (mob.type === 'lancer') {
        mob.health = 200; // Keep him alive for cutscene
        broadcast({ type: 'entity_update', mob: mob });
        if (client) {
            client.send(JSON.stringify({ type: 'deltarune_text', text: [
                "* My bike ran out of fuel!",
                "* I'll get you next time, clowns!",
                "* (Lancer retreats...)"
            ]}));
        }
        setTimeout(() => {
            mob.isDead = true;
            broadcast({ type: 'entity_update', mob: mob });
            if (client) {
                client.send(JSON.stringify({ type: 'deltarune_text', text: [
                    "* Well, that was strange.",
                    "* Come on, let's keep moving forward!"
                ]}));
            }
            setTimeout(() => {
                if (player) {
                    player.x = 80000; player.y = 20; player.z = 80000;
                    if (client) {
                        client.send(JSON.stringify({ type: 'teleport', x: player.x, y: player.y, z: player.z, dim: 'dark_world' }));
                        client.send(JSON.stringify({ type: 'chat', username: 'SYSTEM', message: 'You have entered the Cyber Field.' }));
                    }
                    const pRalsei = mobs.find(m => m.type === 'ralsei' && m.ownerId === player.id);
                    if (pRalsei) { pRalsei.x = player.x + 5; pRalsei.y = player.y; pRalsei.z = player.z; broadcast({ type: 'entity_update', mob: pRalsei }); }
                    const pOwca = mobs.find(m => m.type === 'owca' && m.ownerId === player.id);
                    if (pOwca) { pOwca.x = player.x - 5; pOwca.y = player.y; pOwca.z = player.z; broadcast({ type: 'entity_update', mob: pOwca }); }
                }
            }, 6000);
        }, 8000);
    } else if (mob.type === 'queen') {
            mob.health = 300; 
            broadcast({ type: 'entity_update', mob: mob });
            if (client) {
                client.send(JSON.stringify({ type: 'deltarune_text', text: [
                    "* Okay You Win",
                    "* Here Is Your Currency",
                    "* (You got 100 Emeralds!)",
                    "* Wait...",
                    "* Who Is That Television Man?"
                ]}));
                if (player) {
                    player.inventory['emerald'] = (player.inventory['emerald'] || 0) + 100;
                    client.send(JSON.stringify({ type: 'inventory_update', inventory: player.inventory }));
                }
            }
            setTimeout(() => {
                mob.isDead = true;
                if (player) {
                    for (const k of worldBlocks.keys()) { if (k.endsWith(',dark_world')) worldBlocks.delete(k); }
                    for (let i = mobs.length - 1; i >= 0; i--) { if (mobs[i].dim === 'dark_world' && !mobs[i].inParty) mobs[i].isDead = true; }
                    broadcast({ type: 'reset_dimension', dim: 'dark_world' });
                    
                    // Build Ch 3 Room and Sync to Client
                    const updates = [];
                    for(let x=-10; x<=10; x++) { 
                        for(let z=-10; z<=10; z++) { 
                            addBlock(x*5, 0, z*5, 'obsidian', 'dark_world'); 
                            updates.push({ x: x*5, y: 0, z: z*5, type: 'obsidian', dim: 'dark_world' });
                        } 
                    }
                    if (updates.length > 0) broadcast({ type: 'world_sync', modifications: updates });

                    const t = spawnMob('tenna', 0, 5, 20, 'dark_world');
                    t.tennaEncounter = true;
                    
                    player.x = 0; player.y = 20; player.z = 0; player.dim = 'dark_world';
                    if (client) {
                        client.send(JSON.stringify({ type: 'teleport', x: 0, y: 20, z: 0, dim: 'dark_world' }));
                        client.send(JSON.stringify({ type: 'chat', username: 'SYSTEM', message: 'You have entered Mike\'s Studio.' }));
                    }
                    
                    const pRalsei = mobs.find(m => m.type === 'ralsei' && m.ownerId === player.id);
                    if (pRalsei) { pRalsei.x = 5; pRalsei.y = 20; pRalsei.z = 0; broadcast({ type: 'entity_update', mob: pRalsei }); }
                    const pOwca = mobs.find(m => m.type === 'owca' && m.ownerId === player.id);
                    if (pOwca) { pOwca.x = -5; pOwca.y = 20; pOwca.z = 0; broadcast({ type: 'entity_update', mob: pOwca }); }
                }
            }, 8000);
        } else if (mob.type === 'titan') {
        mob.health = 500; 
        broadcast({ type: 'entity_update', mob: mob });
        if (client) {
            client.send(JSON.stringify({ type: 'deltarune_text', text: [
                "* The Titan falls.",
                "* You got 100 Emeralds!",
                "* The Dark Fountain is sealing..."
            ]}));
            if (player) {
                player.inventory['emerald'] = (player.inventory['emerald'] || 0) + 100;
                client.send(JSON.stringify({ type: 'inventory_update', inventory: player.inventory }));
            }
        }
        setTimeout(() => {
            mob.isDead = true;
            if (player) {
                player.x = 0; player.y = 60; player.z = 0; player.dim = 'overworld';
                if (client) client.send(JSON.stringify({ type: 'teleport', x: 0, y: 60, z: 0, dim: 'overworld' }));
                
                const pRalsei = mobs.find(m => m.type === 'ralsei' && m.ownerId === player.id);
                if (pRalsei) { pRalsei.dim = 'overworld'; pRalsei.x = 5; pRalsei.y = 60; pRalsei.z = 0; broadcast({ type: 'entity_update', mob: pRalsei }); }
                const pOwca = mobs.find(m => m.type === 'owca' && m.ownerId === player.id);
                if (pOwca) { pOwca.dim = 'overworld'; pOwca.x = -5; pOwca.y = 60; pOwca.z = 0; broadcast({ type: 'entity_update', mob: pOwca }); }
                
                for (const k of worldBlocks.keys()) { if (k.endsWith(',dark_world')) worldBlocks.delete(k); }
                for (let i = mobs.length - 1; i >= 0; i--) { if (mobs[i].dim === 'dark_world' && !mobs[i].inParty) mobs[i].isDead = true; }
                broadcast({ type: 'reset_dimension', dim: 'dark_world' });
                generateDarkWorldServer(); 
            }
        }, 8000);
    } else {
        mob.isDead = true; 
        broadcast({ type: 'entity_update', mob: mob });
    }
}

function damagePlayerInBattle(pl, amount) {
    if (pl.battleId) {
        const mob = mobs.find(m => m.id === pl.battleId);
        if (mob && mob.battle && mob.battle.active) {
            let targets = [{type: 'player', ref: pl}];
            const pRalsei = mobs.find(m => m.type === 'ralsei' && m.inParty && m.ownerId === pl.id && !m.isDead && m.health > 0);
            if (pRalsei) targets.push({type: 'mob', ref: pRalsei});
            const pOwca = mobs.find(m => m.type === 'owca' && m.ownerId === pl.id && !m.isDead && m.health > 0);
            if (pOwca) targets.push({type: 'mob', ref: pOwca});
            
            const target = targets[Math.floor(Math.random() * targets.length)];
            if (target.type === 'player') {
                target.ref.health -= amount;
                if (target.ref.health < 0) target.ref.health = 0;
                const client = getClientById(target.ref.id);
                if (client) client.send(JSON.stringify({ type: 'damage', health: target.ref.health }));
                
                const completelyDead = (target.ref.health <= 0) && (!pRalsei || pRalsei.health <= 0) && (!pOwca || pOwca.health <= 0);
                if (completelyDead) {
                    if (target.ref.in2FAFlow) fail2FAServer(target.ref);
                    else {
                        target.ref.health = 20; target.ref.x=0; target.ref.y=60; target.ref.z=0;
                        if (client) client.send(JSON.stringify({ type: 'respawn', x:0, y:60, z:0 }));
                    }
                    endDeltaruneBattle(mob);
                } else {
                    sendBattleState(target.ref, mob, 'update_hp');
                }
            } else {
                target.ref.health -= (amount * 3); // Party takes scaling damage
                if (target.ref.health < 0) target.ref.health = 0;
                broadcast({ type: 'entity_update', mob: target.ref });
                sendBattleState(pl, mob, 'update_hp');
            }
            return true; 
        }
    }
    return false; 
}

function generate2FAArenaServer(cx, cy, cz) {
    const dim = 'pocket_2fa';
    const radius = 15;
    const updates = [];
    
    // Optimization: check if already generated for this coordinate
    if (worldBlocks.has(getKey(cx, cy - BLOCK_SIZE, cz, dim))) return;

    for(let x=-radius; x<=radius; x++) {
        for(let z=-radius; z<=radius; z++) {
            const dist = Math.sqrt(x*x + z*z);
            if (dist <= radius) {
                const bx = cx + x*BLOCK_SIZE;
                const bz = cz + z*BLOCK_SIZE;
                
                addBlock(bx, cy - BLOCK_SIZE, bz, 'bedrock', dim);
                updates.push({ x: bx, y: cy - BLOCK_SIZE, z: bz, type: 'bedrock', dim });
                
                if (dist > radius - 1) {
                    for(let py=0; py<4; py++) {
                        addBlock(bx, cy + py*BLOCK_SIZE, bz, 'obsidian', dim);
                        updates.push({ x: bx, y: cy + py*BLOCK_SIZE, z: bz, type: 'obsidian', dim });
                    }
                    addBlock(bx, cy + 4*BLOCK_SIZE, bz, 'glowstone', dim);
                    updates.push({ x: bx, y: cy + 4*BLOCK_SIZE, z: bz, type: 'glowstone', dim });
                } else if (Math.random() < 0.02) {
                    const h = Math.floor(Math.random() * 3) + 1;
                    for(let py=0; py<h; py++) {
                        addBlock(bx, cy + py*BLOCK_SIZE, bz, 'bedrock', dim);
                        updates.push({ x: bx, y: cy + py*BLOCK_SIZE, z: bz, type: 'bedrock', dim });
                    }
                }
            }
        }
    }
    
    if (updates.length > 0) {
        broadcast({ type: 'world_sync', modifications: updates });
    }
}

function generateCitadel(cx, cy, cz, dim) {
    console.log(`Generating Citadel at ${cx}, ${cy}, ${cz}`);
    // Base Platform (11x11)
    for(let x=-5; x<=5; x++) {
        for(let z=-5; z<=5; z++) {
            addBlock(cx + x*BLOCK_SIZE, cy, cz + z*BLOCK_SIZE, 'nether_brick', dim);
        }
    }
    
    // Pillars at corners
    const corners = [[-5,-5], [5,-5], [-5,5], [5,5]];
    corners.forEach(c => {
        for(let y=1; y<=5; y++) {
            addBlock(cx + c[0]*BLOCK_SIZE, cy + y*BLOCK_SIZE, cz + c[1]*BLOCK_SIZE, 'nether_brick', dim);
        }
        addBlock(cx + c[0]*BLOCK_SIZE, cy + 6*BLOCK_SIZE, cz + c[1]*BLOCK_SIZE, 'glowstone', dim);
    });

    // Central Spawner Altar
    addBlock(cx, cy + 1*BLOCK_SIZE, cz, 'nether_brick', dim);
    addBlock(cx, cy + 2*BLOCK_SIZE, cz, '2fa_block', dim);
    // The Spawner
    addBlock(cx, cy + 3*BLOCK_SIZE, cz, 'spawner', dim);
    spawners.push({ x: cx, y: cy + 3*BLOCK_SIZE, z: cz, dim: dim, timer: 0, mobType: 'blaze' });

    // Roof Ring
    for(let x=-3; x<=3; x++) {
        for(let z=-3; z<=3; z++) {
            if (Math.abs(x) === 3 || Math.abs(z) === 3) {
                addBlock(cx + x*BLOCK_SIZE, cy + 5*BLOCK_SIZE, cz + z*BLOCK_SIZE, 'nether_brick', dim);
            }
        }
    }
}

function updateSpawners(delta) {
    spawners.forEach(spawner => {
        // Check if spawner block still exists
        const k = getKey(spawner.x, spawner.y, spawner.z, spawner.dim);
        if (!worldBlocks.has(k) || worldBlocks.get(k).type !== 'spawner') {
            // Spawner broken
            spawner.broken = true; 
            return;
        }

        spawner.timer += delta;
        if (spawner.timer < 5.0) return; // Cooldown (5s)

        // Check for nearby player
        let playerNear = false;
        for(let p of players.values()) {
            if (p.dim === spawner.dim) {
                const dist = Math.hypot(p.x - spawner.x, p.y - spawner.y, p.z - spawner.z);
                if (dist < 16 * BLOCK_SIZE) { // 16 block activation range
                    playerNear = true;
                    break;
                }
            }
        }

        if (playerNear) {
            // Count existing mobs of type in area to prevent spam
            const nearbyMobs = mobs.filter(m => 
                !m.isDead && m.type === spawner.mobType && 
                Math.hypot(m.x - spawner.x, m.z - spawner.z) < 20 * BLOCK_SIZE
            ).length;

            if (nearbyMobs < 3) {
                // Spawn!
                spawner.timer = 0;
                
                // Random offset
                const ox = (Math.random() - 0.5) * 8 * BLOCK_SIZE;
                const oz = (Math.random() - 0.5) * 8 * BLOCK_SIZE;
                const spawnX = spawner.x + ox;
                const spawnZ = spawner.z + oz;
                const checkK = getKey(spawner.x + ox, spawner.y, spawner.z + oz, spawner.dim);
                const blockAtSpawn = worldBlocks.get(checkK);
                
                if (!blockAtSpawn || blockAtSpawn.type === 'air' || blockAtSpawn.type === 'water') {
                    // Spawn mob
                    spawnMob(spawner.mobType, spawnX, spawner.y, spawnZ, spawner.dim);
                    
                    // Visual FX
                    broadcast({ type: 'spawner_particles', x: spawner.x, y: spawner.y, z: spawner.z, dim: spawner.dim });
                }
            }
        }
    });
}

function generateEndWorld() {
    const size = 15;
    for (let x = -size; x < size; x++) {
        for (let z = -size; z < size; z++) {
            const dist = Math.sqrt(x*x + z*z);
            if (dist < size - Math.random() * 3) {
                const xp = x * BLOCK_SIZE;
                const zp = z * BLOCK_SIZE;
                addBlock(xp, 0, zp, 'end_stone', 'the_end');
                addBlock(xp, -BLOCK_SIZE, zp, 'end_stone', 'the_end');
            }
        }
    }
    const pillars = [[8, 8], [-8, -8], [8, -8], [-8, 8]];
    pillars.forEach(coord => {
        const h = 5 + Math.floor(Math.random() * 5);
        for(let y=1; y<h; y++) addBlock(coord[0] * BLOCK_SIZE, y * BLOCK_SIZE, coord[1] * BLOCK_SIZE, 'obsidian', 'the_end');
        spawnMob('end_crystal', coord[0] * BLOCK_SIZE, (h) * BLOCK_SIZE + 1.5, coord[1] * BLOCK_SIZE, 'the_end');
    });
    //addBlock(0, BLOCK_SIZE, -5 * BLOCK_SIZE, 'network_block', 'the_end'); Do not generate a network block in multiplayer
    addBlock(0, 0, -5 * BLOCK_SIZE, '2fa_block', 'the_end');
}

function createTree(x, y, z, dim) {
    for(let i=0; i<4; i++) addBlock(x, y + (i*BLOCK_SIZE), z, 'wood', dim);
    const topY = y + (4*BLOCK_SIZE);
    for(let lx=-1; lx<=1; lx++) {
        for(let lz=-1; lz<=1; lz++) {
            for(let ly=0; ly<=1; ly++) {
                    if(lx===0 && lz===0 && ly===0) continue;
                    addBlock(x + (lx*BLOCK_SIZE), topY + (ly*BLOCK_SIZE), z + (lz*BLOCK_SIZE), 'leaves', dim);
            }
        }
    }
    addBlock(x, topY + (2*BLOCK_SIZE), z, 'leaves', dim);
}

// --- FLUID SIMULATION ---
function scheduleFluidUpdate(x, y, z, dim) {
    fluidQueue.add(getKey(x, y, z, dim));
}

function wakeNeighbors(x, y, z, dim) {
    const offsets = [
        {x:0, y:1, z:0}, {x:0, y:-1, z:0},
        {x:1, y:0, z:0}, {x:-1, y:0, z:0},
        {x:0, y:0, z:1}, {x:0, y:0, z:-1}
    ];
    offsets.forEach(o => {
        const k = getKey(x + o.x*BLOCK_SIZE, y + o.y*BLOCK_SIZE, z + o.z*BLOCK_SIZE, dim);
        const b = worldBlocks.get(k);
        if (b && (b.type === 'water' || b.type === 'lava')) {
            fluidQueue.add(k);
        }
    });
}

// --- FLUID SIMULATION ---
let fluidTickTimer = 0;
const FLUID_TICK_RATE = 0.1; // Update fluids every 0.1s (slower flow)

function updateFluids(delta) {
    // Accumulate time to slow down flow
    fluidTickTimer += delta;
    if (fluidTickTimer < FLUID_TICK_RATE) return;
    fluidTickTimer = 0;

    if (fluidQueue.size === 0) return;

    const processing = Array.from(fluidQueue);
    fluidQueue.clear();

    processing.forEach(key => {
        const parts = key.split(',');
        const x = parseInt(parts[0]);
        const y = parseInt(parts[1]);
        const z = parseInt(parts[2]);
        const dim = parts[3];

        const block = worldBlocks.get(key);
        if (!block || (block.type !== 'water' && block.type !== 'lava')) return;

        const level = block.state?.level !== undefined ? block.state.level : 8; // Default to 8
        const type = block.type;

        // 1. Try Flowing Down
        const downY = y - BLOCK_SIZE;
        const downKey = getKey(x, downY, z, dim);
        const downBlock = worldBlocks.get(downKey);

        if (!downBlock || downBlock.type === 'air' || (downBlock.type === type && (downBlock.state?.level || 8) < 8)) {
             // If air, place source. If liquid is not full, fill it.
             if (!downBlock || downBlock.type !== type || (downBlock.state?.level || 8) < 8) {
                addBlock(x, downY, z, type, dim, { level: 8 });
                broadcast({ type: 'block_update', x, y: downY, z, blockType: type, dim, state: { level: 8 } });
                scheduleFluidUpdate(x, downY, z, dim);
                return; 
             }
        }

        // 2. Flowing Sideways (Only if on solid ground or full liquid)
        // If we can't go down, try spreading
        if (level > 1) {
            const offsets = [{x:1, z:0}, {x:-1, z:0}, {x:0, z:1}, {x:0, z:-1}];
            offsets.forEach(o => {
                const nx = x + o.x * BLOCK_SIZE;
                const nz = z + o.z * BLOCK_SIZE;
                const nKey = getKey(nx, y, nz, dim);
                const nBlock = worldBlocks.get(nKey);

                if (!nBlock || nBlock.type === 'air') {
                    // Flow to empty space with decayed strength
                    const newLevel = level - 1;
                    addBlock(nx, y, nz, type, dim, { level: newLevel });
                    broadcast({ type: 'block_update', x: nx, y, z: nz, blockType: type, dim, state: { level: newLevel } });
                    scheduleFluidUpdate(nx, y, nz, dim);
                } else if (nBlock.type === type) {
                    // Equalize or fill if neighbor is much lower
                    const nLevel = nBlock.state?.level || 0;
                    if (nLevel < level - 1) {
                         // Update neighbor to be higher
                         const newLevel = level - 1;
                         addBlock(nx, y, nz, type, dim, { level: newLevel });
                         broadcast({ type: 'block_update', x: nx, y, z: nz, blockType: type, dim, state: { level: newLevel } });
                         scheduleFluidUpdate(nx, y, nz, dim);
                    }
                }
            });
        }
    });
}

// --- LAKE GENERATION ---
function generateLake(dim) {
    console.log("Generating Lake...");

    const cx = (Math.random() > 0.5 ? 1 : -1) * (8 + Math.random() * 8) * BLOCK_SIZE;
    const cz = (Math.random() > 0.5 ? 1 : -1) * (8 + Math.random() * 8) * BLOCK_SIZE;
    const radius = 6 + Math.random() * 6;

    for (let x = -radius; x <= radius; x++) {
        for (let z = -radius; z <= radius; z++) {
            const dist = Math.sqrt(x*x + z*z);
            if (dist > radius) continue;

            const wx = cx + x * BLOCK_SIZE;
            const wz = cz + z * BLOCK_SIZE;
            
            // Bowl shape depth
            const depth = Math.floor(radius - dist) * 0.6; 
            
            // Find surface (IGNORING TREES)
            let surfaceY = -100;
            // Scan from top down
            for(let y=30; y>-10; y--) {
                const k = getKey(Math.round(wx/5)*5, y*5, Math.round(wz/5)*5, dim);
                const block = worldBlocks.get(k);
                // Ignore leaves, wood, and existing water/air when finding "Ground"
                if (block && block.type !== 'air' && block.type !== 'leaves' && block.type !== 'wood' && block.type !== 'cactus') { 
                    surfaceY = y*5; 
                    break; 
                }
            }
            if(surfaceY === -100) continue; // No ground found

            // Carve Air and Fill Water
            for (let d = 0; d < depth + 2; d++) {
                const dy = surfaceY - (d * BLOCK_SIZE);
                const bx = Math.round(wx/5)*5;
                const bz = Math.round(wz/5)*5;

                // 1. Remove whatever is there (Tree parts, dirt, stone)
                const k = getKey(bx, dy, bz, dim);
                if (worldBlocks.has(k)) {
                    worldBlocks.delete(k);
                    broadcast({ type: 'block_update', x: bx, y: dy, z: bz, blockType: 'air', dim });
                }
                
                // 2. Fill Water (only up to slightly below surface)
                if (d > 0) {
                     addBlock(bx, dy, bz, 'water', dim, { level: 8 });
                     broadcast({ type: 'block_update', x: bx, y: dy, z: bz, blockType: 'water', dim, state: { level: 8 } });
                }
                
                // 3. Ensure Solid Bottom
                // If this is the bottom-most layer of the lake, place sand below it
                if (d === Math.floor(depth + 2) - 1 || d > depth) {
                    const belowY = dy - BLOCK_SIZE;
                    const belowK = getKey(bx, belowY, bz, dim);
                    const belowBlock = worldBlocks.get(belowK);
                    // If below is air or water (leaking), plug it with sand
                    if (!belowBlock || belowBlock.type === 'air' || belowBlock.type === 'water' || belowBlock.type === 'leaves') {
                         addBlock(bx, belowY, bz, 'sand', dim);
                         broadcast({ type: 'block_update', x: bx, y: belowY, z: bz, blockType: 'sand', dim });
                    }
                }
            }
        }
        
        // Generate Sky Lift in the center of the lake
        const lakeBx = Math.round(cx/5)*5; const lakeBz = Math.round(cz/5)*5;
        for(let y=30; y>-10; y--) {
            const k = getKey(lakeBx, y*5, lakeBz, dim);
            const b = worldBlocks.get(k);
            if (b && b.type === 'water') {
                addBlock(lakeBx, y*5 + BLOCK_SIZE, lakeBz, 'lily_pad', dim, { isSkyLift: true });
                broadcast({ type: 'block_update', x: lakeBx, y: y*5 + BLOCK_SIZE, z: lakeBz, blockType: 'lily_pad', dim, state: { isSkyLift: true } });
                
                for(let dy=y*5; dy>-50; dy-=BLOCK_SIZE) {
                    const bk = getKey(lakeBx, dy, lakeBz, dim);
                    const bb = worldBlocks.get(bk);
                    if (bb && bb.type !== 'water') {
                        worldBlocks.delete(bk);
                        addBlock(lakeBx, dy, lakeBz, 'magma', dim);
                        broadcast({ type: 'block_update', x: lakeBx, y: dy, z: lakeBz, blockType: 'magma', dim });
                        break;
                    }
                }
                break;
            }
        }
    }
}

function saveWorld(overrideSnapshot = null, filename = 'world_save.json') {
    try {
        const state = {
            blocks: Array.from(worldBlocks.entries()).map(([k, v]) => ({ key: k, val: v })),
            mobs: mobs,
            players: Array.from(players.values()),
            projectiles: projectiles,
            spawners: spawners,
            worldTime: worldTime,
            hostSessionId: players.get(hostId)?.sessionId || hostSessionId,
            hostHTMLSnapshot: overrideSnapshot || hostHTMLSnapshot
        };
        fs.writeFileSync(filename, JSON.stringify(state));
        console.log(`World saved successfully to ${filename}.`);
    } catch (e) {
        console.error(`Failed to save world to ${filename}:`, e);
    }
}

function loadWorld(filename) {
    console.log(`Loading World State from ${filename}...`);
    try {
        const state = JSON.parse(fs.readFileSync(filename, 'utf8'));
        state.blocks.forEach(b => worldBlocks.set(b.key, b.val));
        mobs.push(...state.mobs);
        if (state.players) state.players.forEach(p => pendingSessions.set(p.sessionId, p));
        if (state.projectiles) projectiles.push(...state.projectiles);
        if (state.spawners) spawners.push(...state.spawners);
        hostSessionId = state.hostSessionId;
        worldTime = state.worldTime || 0;
        hostHTMLSnapshot = state.hostHTMLSnapshot;
        return true;
    } catch (e) {
        console.error(`Failed to load world from ${filename}:`, e);
        return false;
    }
}

function initWorld() {
    if (fs.existsSync('anomaly_server_state.json')) {
        console.log("Loading Anomalous Server State (Override)...");
        if (loadWorld('anomaly_server_state.json')) {
            fs.unlinkSync('anomaly_server_state.json');
            saveWorld(); // Persist the anomaly state to standard save
            return;
        }
    } 
    
    if (fs.existsSync('world_save.json')) {
        if (loadWorld('world_save.json')) return;
    } 
    
    console.log("Generating Server World...");
    generateOverworld();
    generateEndWorld();
    generateNether();
    generateDesertMarketServer('overworld');
    generateSkyIslandsServer('overworld');
    generateFrostedTaigaServer('overworld');
    generateDarkWorldServer();
}

function addBlock(x, y, z, type, dim, state = {}) {
    worldBlocks.set(getKey(x,y,z,dim), { type, state });
}

function checkMarketQuestServer(dim) {
    if (dim !== 'overworld') return;
    const cx = 300; const cz = 0; const y = 10;
    
    const b1 = worldBlocks.get(getKey(cx + 15, y + 5, cz + 15, dim));
    const b2 = worldBlocks.get(getKey(cx - 15, y + 5, cz + 15, dim));
    const b3 = worldBlocks.get(getKey(cx, y + 5, cz - 15, dim));

    if (b1 && b1.type === 'packed_ice' && b2 && b2.type === 'red_mushroom' && b3 && b3.type === 'end_stone') {
        const cBlock = worldBlocks.get(getKey(cx, y + 5, cz, dim));
        if (!cBlock || cBlock.type !== 'market_carpet_2') {
            const updates = [];
            for(let dx=-5; dx<=5; dx+=5) {
                for(let dz=-5; dz<=5; dz+=5) {
                    addBlock(cx+dx, y + 5, cz+dz, 'market_carpet_2', dim, { isMagicCarpet: true });
                    updates.push({ x: cx+dx, y: y + 5, z: cz+dz, type: 'market_carpet_2', dim: dim, state: { isMagicCarpet: true } });
                }
            }
            const mx = 50000; const mz = 50000;
            for(let dx=-5; dx<=5; dx+=5) {
                for(let dz=-5; dz<=5; dz+=5) {
                    addBlock(mx+dx, 5, mz+dz, 'market_carpet_2', dim, { isMagicCarpet: true });
                    updates.push({ x: mx+dx, y: 5, z: mz+dz, type: 'market_carpet_2', dim: dim, state: { isMagicCarpet: true } });
                }
            }
            broadcast({ type: 'world_sync', modifications: updates });
            broadcast({ type: 'quest_complete', x: cx, y: y + 5, z: cz, dim });
        }
    }
}

function trySummonDiddyGolemServer(x, y, z, dim) {
    const topKey = getKey(x, y, z, dim);
    const midKey = getKey(x, y - BLOCK_SIZE, z, dim);
    const baseKey = getKey(x, y - 2 * BLOCK_SIZE, z, dim);

    const top = worldBlocks.get(topKey);
    const mid = worldBlocks.get(midKey);
    const base = worldBlocks.get(baseKey);

    if (!top || top.type !== 'obsidian') return false;
    if (!mid || mid.type !== 'dirt') return false;
    if (!base || base.type !== 'dirt') return false;

    worldBlocks.delete(topKey);
    worldBlocks.delete(midKey);
    worldBlocks.delete(baseKey);

    broadcast({ type:'block_update', x, y, z, blockType:'air', dim });
    broadcast({ type:'block_update', x, y: y - BLOCK_SIZE, z, blockType:'air', dim });
    broadcast({ type:'block_update', x, y: y - 2 * BLOCK_SIZE, z, blockType:'air', dim });

    const mob = spawnMob('diddy', x, y + BLOCK_SIZE, z, dim);
    mob.health = 20;
    mob.naturalSpawn = false;
    mob.isGolem = true;

    return true;
}

function spawnMob(type, x, y, z, dim) {
    let health = 3;
    if (type === 'villager' || type === 'merchant' || type === 'mercator') health = 5;
    if (type === 'diddy') health = 4;
    if (type === 'end_crystal') health = 1;
    if (type === 'blaze') health = 20;
    if (type === 'pigman') health = 20;
    if (type === 'voidling') health = 50;
    if (type === 'void_weaver') health = 40;
    if (type === 'void_behemoth') health = 100;
    if (type === 'frostbound') health = 40;
    if (type === 'lynx') health = 15;
    if (type === 'tork') health = 100;
    if (type === 'owca') health = 30;
    if (type === 'ralsei') health = 50;
    if (type === 'lancer') health = 200;
    if (type === 'scc') health = 100;
    if (type === 'queen') health = 300;
    if (type === 'berdly') health = 150;
    
    let trades = [];
    if (type === 'villager') {
        const tradePool = [
            { costItem: 'dirt', costCount: 10, rewardItem: 'emerald', rewardCount: 1 },
            { costItem: 'emerald', costCount: 2, rewardItem: 'door', rewardCount: 1 },
            { costItem: 'stone', costCount: 20, rewardItem: 'emerald', rewardCount: 1 },
            { costItem: 'wooden_slab', costCount: 1, costItem2: 'ice_shard', costCount2: 1, rewardItem: 'ice_knife', rewardCount: 1 },
            { costItem: 'emerald', costCount: 5, rewardItem: 'mysterious_door', rewardCount: 1 },
            { costItem: 'wood', costCount: 10, rewardItem: 'emerald', rewardCount: 1 }
        ];
        trades = tradePool.sort(() => 0.5 - Math.random()).slice(0, 3);
    }
    else if (type === 'merchant') {
            const tradePool = [
                { costItem: 'gold_nugget', costCount: 5, rewardItem: 'healing_salve', rewardCount: 1 },
                { costItem: 'emerald', costCount: 15, rewardItem: 'void_charm', rewardCount: 1 },
                { costItem: 'sand', costCount: 20, rewardItem: 'market_carpet_1', rewardCount: 4 },
                { costItem: 'cobblestone', costCount: 15, rewardItem: 'market_awning', rewardCount: 2 },
                { costItem: 'emerald', costCount: 20, rewardItem: 'spawn_egg_voidling', rewardCount: 1 },
                { costItem: 'void_sign', costCount: 1, costItem2: 'wood', costCount2: 1, rewardItem: 'void_sign', rewardCount: 2 }
            ];
            trades = tradePool.sort(() => 0.5 - Math.random()).slice(0, 4);
        }
        else if (type === 'mercator') {
            trades = [
                { costItem: 'emerald', costCount: 5, rewardItem: 'lead_flask', rewardCount: 1 },
                { costItem: 'emerald', costCount: 5, rewardItem: 'helium_flask', rewardCount: 1 },
                { costItem: 'emerald', costCount: 5, rewardItem: 'midas_flask', rewardCount: 1 },
                { costItem: 'emerald', costCount: 5, rewardItem: 'martyr_flask', rewardCount: 1 },
                { costItem: 'emerald', costCount: 5, rewardItem: 'determination_flask', rewardCount: 1 }
            ];
        }
        else if (type === 'tork') {
            trades = [
                { costItem: 'packed_ice', costCount: 10, rewardItem: 'void_charm', rewardCount: 1 },
                { costItem: 'void_charm', costCount: 1, rewardItem: 'emerald', rewardCount: 15 },
                { costItem: 'emerald', costCount: 5, rewardItem: 'corrupted_2fa_block', rewardCount: 1 },
                { costItem: 'dirt', costCount: 32, rewardItem: 'hammer', rewardCount: 1 }
            ];
        }

    const mob = {
        id: Math.random().toString(36).substr(2, 9),
        type: type,
        x: x, y: y, z: z,
        vx: 0, vy: 0, vz: 0,
        dim: dim,
        yaw: 0,
        isDead: false,
        lookAt: {x: 0, y: 0, z: 0},
        health: health,
        lastAttackTime: 0,
        lastDamageTime: 0,
        aiState: { mode: 'idle', target: null, timer: 0 }, 
        trades: trades,
        // Blaze Specific
        chargeTick: 0,
        isCharging: false,
        shotsFired: 0,
        shotTimer: 0,
        // Sulfur Cube Specific
        archetype: 'default',
        eatenBlock: null,
        explodeTimer: 0,
        inParty: false,
        ownerId: null
    };
    mobs.push(mob);
    return mob;
}

// --- HELPER: Check for Direct Sunlight (High sky check) ---
function isExposedToSun(x, y, z, dim) {
    const bx = Math.round(x / BLOCK_SIZE) * BLOCK_SIZE;
    const bz = Math.round(z / BLOCK_SIZE) * BLOCK_SIZE;
    // Start checking from just above the entity
    const startY = Math.round(y / BLOCK_SIZE) * BLOCK_SIZE + BLOCK_SIZE;
    
    // Check up to height 200 (arbitrary sky limit)
    for(let checkY = startY; checkY < 200; checkY += BLOCK_SIZE) {
        const k = getKey(bx, checkY, bz, dim);
        const block = worldBlocks.get(k);
        if (block && block.type !== 'air' && block.type !== 'barrier') {
             // Leaves usually block sunlight in MC logic, so we treat them as cover
            return false;
        }
    }
    return true;
}

function fail2FAServer(player) {
    player.in2FAFlow = false;
    player.totpSecret = null;
    
    // Kill auth zombies
    if (player.authZombies) {
        player.authZombies.forEach(zid => {
            const m = mobs.find(mob => mob.id === zid);
            if (m) {
                m.isDead = true;
                broadcast({ type: 'entity_update', mob: m });
            }
        });
    }
    
    // Respawn in previous world
    player.health = 20;
    player.dim = player.pre2FAPos.dim;
    player.x = 0; player.y = 60; player.z = 0;
    
    const client = getClientById(player.id);
    if (client) {
        client.send(JSON.stringify({ type: 'respawn', x: 0, y: 60, z: 0 }));
        client.send(JSON.stringify({ type: 'teleport', x: 0, y: 60, z: 0, dim: player.dim }));
        client.send(JSON.stringify({ type: 'chat', username: 'SYSTEM', message: '2FA FAILED: You have died or timed out.' }));
        client.send(JSON.stringify({ type: 'close_totp' }));
    }
}

function start2FAServer(player) {
    player.in2FAFlow = true;
    player.pre2FAPos = { x: player.x, y: player.y, z: player.z, dim: player.dim };
    
    // Give each player their own offset arena in the pocket dimension
    const arenaX = 1000 + (Array.from(players.values()).indexOf(player) * 100 * BLOCK_SIZE);
    const arenaY = 50 * BLOCK_SIZE;
    generate2FAArenaServer(arenaX, arenaY, 0);
    
    player.dim = 'pocket_2fa';
    player.x = arenaX; player.y = arenaY + BLOCK_SIZE; player.z = 0;
    player.vx = 0; player.vy = 0; player.vz = 0;
    
    player.authZombies = [];
    for(let i=0; i<3; i++) {
        const z = spawnMob('zombie', arenaX + (Math.random()-0.5)*10, arenaY + 5*BLOCK_SIZE, (Math.random()-0.5)*10, 'pocket_2fa');
        player.authZombies.push(z.id);
    }
    
    const client = getClientById(player.id);
    if (client) {
        client.send(JSON.stringify({ type: 'teleport', x: player.x, y: player.y, z: player.z, dim: player.dim }));
        client.send(JSON.stringify({ type: 'chat', username: 'SYSTEM', message: '2FA INITIALIZED: Defeat 3 Zombies to authenticate.' }));
    }
}

function checkHazardDamage(entity) {
    let feetY = entity.y;
    if (entity.username) feetY = entity.y - 10;

    const bx = Math.round(entity.x / BLOCK_SIZE) * BLOCK_SIZE;
    const by = Math.round(feetY / BLOCK_SIZE) * BLOCK_SIZE;
    const bz = Math.round(entity.z / BLOCK_SIZE) * BLOCK_SIZE;

    for (let ox = -1; ox <= 1; ox++) {
        for (let oy = -1; oy <= 1; oy++) {
            for (let oz = -1; oz <= 1; oz++) {
                const blockX = bx + ox * BLOCK_SIZE;
                const blockY = by + oy * BLOCK_SIZE;
                const blockZ = bz + oz * BLOCK_SIZE;
                const k = getKey(blockX, blockY, blockZ, entity.dim);
                const block = worldBlocks.get(k);

                if (block) {
                    const type = block.type;
                    if (type === 'magma' || type === 'cactus' || type === 'lava' || type === '2fa_block') {
                        const dx = Math.abs(entity.x - blockX);
                        const dz = Math.abs(entity.z - blockZ);
                        const dy = feetY - blockY;

                        let hit = false;
                        if (type === 'magma') {
                            if (dx < 4 && dz < 4 && dy > -2 && dy < 6) hit = true;
                        } else if (type === 'cactus' || type === 'lava' || type === '2fa_block') {
                            if (dx < 4 && dz < 4 && dy > -2 && dy < 6) hit = true;
                        }

                        if (hit) {
                            if (type === '2fa_block') {
                                if ((entity.type && entity.type.startsWith('void')) || entity.type === 'owca') {
                                    worldBlocks.set(k, { type: 'corrupted_2fa_block', state: {} });
                                    broadcast({ type: 'block_update', x: blockX, y: blockY, z: blockZ, blockType: 'corrupted_2fa_block', dim: entity.dim });
                                    createVoidExplosion(blockX, blockY, blockZ, entity.dim);
                                    if (entity.type === 'owca') {
                                        entity.health = 30; entity.x += 10000;
                                    } else {
                                        entity.isDead = true;
                                    }
                                    broadcast({ type: 'entity_update', mob: entity });
                                    return false; 
                                }
                                if (entity.username && !entity.in2FAFlow && !entity.authenticated) {
                                    start2FAServer(entity);
                                }
                                return false; // Does not deal standard damage
                            }
                            
                            if (type === 'corrupted_2fa_block') {
                                entity.vy = 120; // Extreme Void Trampoline
                                broadcast({ type: 'entity_update', mob: entity });
                                return false;
                            }

                            const now = performance.now();
                            if (now - (entity.lastDamageTime || 0) > 500) {
                                entity.health--;
                                if (entity.health <= 0 && !entity.username) entity.isDead = true;
                                entity.lastDamageTime = now;
                                return true;
                            }
                        }
                    }
                }
            }
        }
    }
    return false;
}

function createVoidExplosion(x, y, z, dim) {
    const damageRadius = 15;
    players.forEach(p => {
        if (p.dim !== dim || p.mode === 'creative') return;
        const dist = Math.hypot(p.x - x, p.y - y, p.z - z);
        if (dist < damageRadius) {
            const dmg = p.authenticated ? 3 : 15; // Auth players resist void energy
            p.health -= dmg;
            const client = getClientById(p.id);
            if (client) client.send(JSON.stringify({ type: 'damage', health: p.health }));
            if (p.health <= 0) {
                if (p.in2FAFlow) fail2FAServer(p);
                else {
                    p.health = 20; p.x = 0; p.y = 60; p.z = 0;
                    if (client) client.send(JSON.stringify({ type: 'respawn', x:0, y:60, z:0 }));
                }
            }
        }
    });
    broadcast({ type: 'void_explosion', x, y, z, dim });
}

function createExplosion(x, y, z, dim, radius) {
    const damageRadius = radius * 2.5;
    
    players.forEach(p => {
        if (p.dim !== dim || p.mode === 'creative') return;
        const dist = Math.hypot(p.x - x, p.y - y, p.z - z);
        if (dist < damageRadius) {
            const dmg = Math.floor((1 - dist/damageRadius) * 20);
            if (dmg > 0) {
                p.health -= dmg;
                const client = getClientById(p.id);
                if (client) client.send(JSON.stringify({ type: 'damage', health: p.health }));
                if (p.health <= 0) {
                    if (p.in2FAFlow) fail2FAServer(p);
                    else {
                        p.health = 20;
                        p.x = 0; p.y = 60; p.z = 0;
                        if (client) client.send(JSON.stringify({ type: 'respawn', x:0, y:60, z:0 }));
                    }
                }
            }
        }
    });

    mobs.forEach(m => {
        if (m.dim !== dim || m.isDead || m.type === 'end_crystal') return;
        const dist = Math.hypot(m.x - x, m.y - y, m.z - z);
        if (dist < damageRadius) {
            const dmg = Math.floor((1 - dist/damageRadius) * 20);
            if (dmg > 0) {
                m.health -= dmg;
                if (m.health <= 0) m.isDead = true;
                broadcast({ type: 'entity_update', mob: m });
            }
        }
    });

    const updates = [];
    const r = Math.ceil(radius);
    const centerBx = Math.round(x / BLOCK_SIZE) * BLOCK_SIZE;
    const centerBy = Math.round(y / BLOCK_SIZE) * BLOCK_SIZE;
    const centerBz = Math.round(z / BLOCK_SIZE) * BLOCK_SIZE;

    for (let bx = centerBx - r*BLOCK_SIZE; bx <= centerBx + r*BLOCK_SIZE; bx+=BLOCK_SIZE) {
        for (let by = centerBy - r*BLOCK_SIZE; by <= centerBy + r*BLOCK_SIZE; by+=BLOCK_SIZE) {
            for (let bz = centerBz - r*BLOCK_SIZE; bz <= centerBz + r*BLOCK_SIZE; bz+=BLOCK_SIZE) {
                const dist = Math.hypot(bx - x, by - y, bz - z);
                if (dist <= radius * BLOCK_SIZE) {
                    const k = getKey(bx, by, bz, dim);
                    const blockData = worldBlocks.get(k);
                    if (blockData && !UNBREAKABLE_BLOCKS.includes(blockData.type) && blockData.type !== 'air') {
                        worldBlocks.delete(k); 
                        updates.push({ x: bx, y: by, z: bz, type: 'air', dim: dim });
                    }
                }
            }
        }
    }

    if (updates.length > 0) {
        broadcast({ type: 'world_sync', modifications: updates });
    }
    broadcast({ type: 'explosion', x, y, z, dim });
}

function attemptLynxSpawning() {
    const count = mobs.filter(m => !m.isDead && m.type === 'lynx').length;
    if (count >= 1) return;
    
    if (Math.random() < 0.05) {
        const sx = 20000 + (Math.random()-0.5) * 40 * BLOCK_SIZE;
        const sz = 20000 + (Math.random()-0.5) * 40 * BLOCK_SIZE;
        const checkX = Math.round(sx/BLOCK_SIZE)*BLOCK_SIZE;
        const checkZ = Math.round(sz/BLOCK_SIZE)*BLOCK_SIZE;
        let spawnY = -1000;
        
        for(let y = 130 * BLOCK_SIZE; y > 115 * BLOCK_SIZE; y -= BLOCK_SIZE) {
            const b = worldBlocks.get(getKey(checkX,y,checkZ,'overworld'));
            if (b && b.type !== 'air' && b.type !== 'leaves' && b.type !== 'flower_pink' && b.type !== 'flower_white') { 
                spawnY = y + BLOCK_SIZE; break; 
            }
        }
        
        if (spawnY > 110 * BLOCK_SIZE) spawnMob('lynx', checkX, spawnY, checkZ, 'overworld');
    }
}

function attemptMercatorSpawning() {
    const count = mobs.filter(m => !m.isDead && m.type === 'mercator').length;
    if (count >= 4) return;
    
    if (Math.random() < 0.05) {
        const sx = 50000 + (Math.random()-0.5) * 100;
        const sz = 50000 + (Math.random()-0.5) * 100;
        const checkX = Math.round(sx/BLOCK_SIZE)*BLOCK_SIZE;
        const checkZ = Math.round(sz/BLOCK_SIZE)*BLOCK_SIZE;
        let spawnY = -1000;
        
        for(let y = 30 * BLOCK_SIZE; y > -10 * BLOCK_SIZE; y -= BLOCK_SIZE) {
            const b = worldBlocks.get(getKey(checkX,y,checkZ,'overworld'));
            if (b && b.type !== 'air' && b.type !== 'market_awning' && !b.type.includes('carpet')) { 
                spawnY = y + BLOCK_SIZE; break; 
            }
        }
        
        if (spawnY > -900) spawnMob('mercator', checkX, spawnY, checkZ, 'overworld');
    }
}

function attemptSulfurCubeSpawning() {
    const count = mobs.filter(m => !m.isDead && m.type === 'sulfur_cube').length;
    if (count >= 4) return;
    
    if (Math.random() < 0.05) {
        const sx = (Math.random()-0.5) * 20 * BLOCK_SIZE;
        const sz = (Math.random()-0.5) * 20 * BLOCK_SIZE;
        
        const checkX = Math.round(sx/BLOCK_SIZE)*BLOCK_SIZE;
        const checkZ = Math.round(sz/BLOCK_SIZE)*BLOCK_SIZE;
        let spawnY = -1000;
        
        for(let y = -95 * BLOCK_SIZE; y > -130 * BLOCK_SIZE; y -= BLOCK_SIZE) {
            const b = worldBlocks.get(getKey(checkX,y,checkZ,'overworld'));
            if (b && b.type !== 'air') { spawnY = y + BLOCK_SIZE; break; }
        }
        
        if (spawnY > -900) spawnMob('sulfur_cube', checkX, spawnY, checkZ, 'overworld');
    }
}

function attemptCaveMobSpawning() {
    // Limit to 5 cave zombies
    const caveZombies = mobs.filter(m => !m.isDead && m.type === 'zombie' && m.isCaveZombie).length;
    if (caveZombies >= 5) return;

    if (Math.random() < 0.05) {
        const activePlayers = Array.from(players.values()).filter(p => p.dim === 'overworld');
        if (activePlayers.length === 0) return;

        // Random position within the Abyss (radius ~15)
        const angle = Math.random() * Math.PI * 2;
        const dist = Math.random() * 15 * BLOCK_SIZE;
        const checkX = Math.round((Math.cos(angle) * dist) / BLOCK_SIZE) * BLOCK_SIZE;
        const checkZ = Math.round((Math.sin(angle) * dist) / BLOCK_SIZE) * BLOCK_SIZE;

        // Start scanning from a random depth in the cave
        const startY = -Math.random() * 75 * BLOCK_SIZE;
        let spawnY = -1000;

        for(let y = Math.round(startY / BLOCK_SIZE) * BLOCK_SIZE; y > -85 * BLOCK_SIZE; y -= BLOCK_SIZE) {
             const blockData = worldBlocks.get(getKey(checkX, y, checkZ, 'overworld'));
             if (blockData && blockData.type !== 'air' && blockData.type !== 'water' && blockData.type !== 'lava') {
                 spawnY = y + BLOCK_SIZE;
                 break;
             }
        }

        if (spawnY > -900) {
            const newMob = spawnMob('zombie', checkX, spawnY, checkZ, 'overworld');
            newMob.naturalSpawn = true; // Tag for sunlight burning
            newMob.isCaveZombie = true; // Tag for spawn limit
        }
    }
}

function attemptVoidlingSpawning() {
    const activePlayers = Array.from(players.values());
    if (activePlayers.length === 0) return;
    const p = activePlayers[Math.floor(Math.random() * activePlayers.length)];
    
    const isMarket = p.x > 40000 && p.z > 40000;
    const count = mobs.filter(m => !m.isDead && m.type.startsWith('void')).length;
    const limit = isMarket ? 8 : 3;
    if (count >= limit) return;
    
    const timeRatio = (worldTime % DAY_DURATION) / DAY_DURATION;
    const isEnd = p.dim === 'the_end';
    const isDeepAbyss = p.y < -80 * BLOCK_SIZE;
    const isOverworldNight = p.dim === 'overworld' && (timeRatio > 0.45 && timeRatio < 0.95);

    if (!isEnd && !isDeepAbyss && !isOverworldNight) return;

    const spawnChance = isMarket ? 0.05 : 0.005;
    if (Math.random() < spawnChance) {
        const angle = Math.random() * Math.PI * 2;
        const dist = 20 * BLOCK_SIZE + Math.random() * 20 * BLOCK_SIZE;
        const checkX = Math.round((p.x + Math.cos(angle) * dist) / BLOCK_SIZE) * BLOCK_SIZE;
        const checkZ = Math.round((p.z + Math.sin(angle) * dist) / BLOCK_SIZE) * BLOCK_SIZE;

        let spawnY = p.y + 10 * BLOCK_SIZE;
        if (isMarket && Math.random() > 0.5) spawnY = 2 * BLOCK_SIZE; // Drop them under the roof
        
        const types = ['voidling', 'void_weaver', 'void_behemoth'];
        const type = types[Math.floor(Math.random() * types.length)];
        spawnMob(type, checkX, spawnY, checkZ, p.dim);
    }
}

function attemptNaturalMobSpawning() {
    const timeRatio = (worldTime % DAY_DURATION) / DAY_DURATION;
    
    const activePlayers = Array.from(players.values()).filter(p => p.dim === 'overworld');
    if (activePlayers.length === 0) return;
    const p = activePlayers[Math.floor(Math.random() * activePlayers.length)];
    
    const isTaiga = p.x < -600;
    if (timeRatio < 0.5 && !isTaiga) return;
    
    const naturalMobs = mobs.filter(m => !m.isDead && !m.isCaveZombie && m.type !== 'merchant' && m.type !== 'villager');
    const taigaMobs = naturalMobs.filter(m => m.x < -600).length;
    const regularMobs = naturalMobs.filter(m => m.x >= -600).length;

    if (isTaiga && taigaMobs >= 50) return;
    if (!isTaiga && regularMobs >= 50) return;

    if (Math.random() < 0.05) {
        
        const angle = Math.random() * Math.PI * 2;
        const dist = 15 * BLOCK_SIZE + Math.random() * 15 * BLOCK_SIZE;
        const sx = p.x + Math.cos(angle) * dist;
        const sz = p.z + Math.sin(angle) * dist;

        let spawnY = -1000;
        const checkX = Math.round(sx / BLOCK_SIZE) * BLOCK_SIZE;
        const checkZ = Math.round(sz / BLOCK_SIZE) * BLOCK_SIZE;
        const isMarket = checkX > 40000 && checkZ > 40000;

        for(let y=30 * BLOCK_SIZE; y > -90 * BLOCK_SIZE; y-=BLOCK_SIZE) {
             const blockData = worldBlocks.get(getKey(checkX, y, checkZ, 'overworld'));
             if (blockData && blockData.type !== 'air') {
                 if (isMarket && (blockData.type === 'stick_roof' || blockData.type === 'market_awning') && Math.random() > 0.3) {
                     continue; // 70% chance to pierce through roof to spawn inside market
                 }
                 spawnY = y + BLOCK_SIZE;
                 break;
             }
        }

        if (spawnY > -900) {
            if (checkX > 40000 && checkZ > 40000 && Math.random() > 0.2) return; // Reduce market zombies
            const spawnType = Math.random() < 0.2 ? 'diddy' : 'zombie';
            const newMob = spawnMob(spawnType, checkX, spawnY, checkZ, 'overworld');
            newMob.naturalSpawn = true;
        }
    }
}

// --- SERVER-SIDE VILLAGER AI ---
function updateVillagerAI(mob, delta, timeRatio) {
    // Only AI for villagers in overworld
    if ((mob.type !== 'villager' && mob.type !== 'mercator') || mob.dim !== 'overworld') return;

    // --- MERCATOR SPECIFIC AI ---
    if (mob.type === 'mercator') {
        if (mob.tradingWith) {
            mob.vx = 0; mob.vz = 0;
            const p = players.get(mob.tradingWith);
            if (p) mob.yaw = Math.atan2(p.x - mob.x, p.z - mob.z);
            return;
        }
        if (!mob.aiState) mob.aiState = { mode: 'wandering', target: null, timer: 0 };
        mob.aiState.timer -= delta;
        if (mob.aiState.timer <= 0) {
            mob.aiState.timer = 5 + Math.random() * 10;
            mob.aiState.target = { x: 50000 + (Math.random() - 0.5) * 100, z: 50000 + (Math.random() - 0.5) * 100 };
        }
        if (mob.aiState.target) {
            const dx = mob.aiState.target.x - mob.x; const dz = mob.aiState.target.z - mob.z;
            const dist = Math.hypot(dx, dz);
            if (dist > 3) {
                mob.vx = (dx / dist) * 12; mob.vz = (dz / dist) * 12;
                mob.yaw = Math.atan2(dx, dz);
                
                // Simple Auto Jump for Mercators
                const lookX = mob.x + (dx/dist) * 3;
                const lookZ = mob.z + (dz/dist) * 3;
                const bx = Math.round(lookX / BLOCK_SIZE) * BLOCK_SIZE;
                const by = Math.round(mob.y / BLOCK_SIZE) * BLOCK_SIZE;
                const bz = Math.round(lookZ / BLOCK_SIZE) * BLOCK_SIZE;
                const wallBlock = worldBlocks.get(getKey(bx, by, bz, mob.dim));
                if (wallBlock && wallBlock.type !== 'air' && !wallBlock.type.includes('door') && mob.vy === 0) {
                    mob.vy = 25;
                }
            } else { mob.vx = 0; mob.vz = 0; }
        }
        return;
    }

    // --- NEW: TRADING FREEZE ---
    if (mob.tradingWith) {
        mob.vx = 0;
        mob.vz = 0;
        // Optionally turn to face player (requires knowing player position)
        const p = players.get(mob.tradingWith);
        if (p) {
            const dx = p.x - mob.x;
            const dz = p.z - mob.z;
            mob.yaw = Math.atan2(dx, dz);
        }
        return;
    }

    if (!mob.aiState) mob.aiState = { mode: 'idle', target: null, timer: 0 };
    mob.aiState.timer -= delta;

    // FIX: Extend night time to 0.99 so they stay in while zombies burn (0.95+)
    const isNight = timeRatio > 0.45 && timeRatio < 0.99;

    // 1. DECISION MAKING
    if (isNight && mob.aiState.mode !== 'sleeping') {
        mob.aiState.mode = 'sleeping';
        if (villagePOIs.length > 0) {
            const houses = villagePOIs.filter(p => p.type === 'house');
            if (houses.length > 0) {
                mob.aiState.target = houses[Math.floor(Math.random() * houses.length)];
            }
        }
    } 
    else if (!isNight && mob.aiState.mode === 'sleeping') {
        mob.aiState.mode = 'idle';
        mob.aiState.timer = 0; 
    }

    if (!isNight && mob.aiState.timer <= 0) {
        mob.aiState.timer = 5 + Math.random() * 15; 
        const roll = Math.random();
        if (roll < 0.6) {
            mob.aiState.mode = 'farming';
            const farms = villagePOIs.filter(p => p.type === 'farm');
            if (farms.length > 0) mob.aiState.target = farms[Math.floor(Math.random() * farms.length)];
        } else {
            mob.aiState.mode = 'wandering';
            const targetX = 300 * BLOCK_SIZE + (Math.random() - 0.5) * 100; 
            const targetZ = 0 + (Math.random() - 0.5) * 100;
            mob.aiState.target = { x: targetX, z: targetZ };
        }
    }

    // 2. MOVEMENT
    if (mob.aiState.target) {
        // Use mesh position for client, raw x/z for server
        const currentX = mob.x !== undefined ? mob.x : mob.mesh.position.x;
        const currentZ = mob.z !== undefined ? mob.z : mob.mesh.position.z;
        const currentY = mob.y !== undefined ? mob.y : mob.mesh.position.y;
        
        const tx = mob.aiState.target.x;
        const tz = mob.aiState.target.z;
        const dx = tx - currentX;
        const dz = tz - currentZ;
        const dist = Math.sqrt(dx*dx + dz*dz);

        if (dist > 3) { 
            const speed = 15;
            // Update velocity
            if (mob.vx !== undefined) {
                // Server object
                mob.vx = (dx / dist) * speed;
                mob.vz = (dz / dist) * speed;
                mob.yaw = Math.atan2(dx, dz);
            } else {
                // Client object
                mob.velocity.x = (dx / dist) * speed;
                mob.velocity.z = (dz / dist) * speed;
                mob.mesh.lookAt(tx, currentY, tz);
            }

            // --- JUMP / COLLISION LOGIC ---
            const lookX = currentX + (dx/dist) * 3;
            const lookZ = currentZ + (dz/dist) * 3;
            const bx = Math.round(lookX / BLOCK_SIZE) * BLOCK_SIZE;
            const by = Math.round(currentY / BLOCK_SIZE) * BLOCK_SIZE;
            const bz = Math.round(lookZ / BLOCK_SIZE) * BLOCK_SIZE;
            
            // 1. Cactus Check (Body Level)
            const wallKey = getKey(bx, by, bz, mob.dim);
            const wallBlock = worldBlocks.get(wallKey);
            if (wallBlock && wallBlock.type === 'cactus') {
                mob.vx *= -1; mob.vz *= -1; mob.aiState.timer = 0; return;
            }

            // 2. Void/Cliff Check (Feet Level)
            let hasFloor = false;
            for (let y = by - BLOCK_SIZE; y > -601; y -= BLOCK_SIZE) {
                const floorKey = getKey(bx, y, bz, mob.dim);
                const floorBlock = worldBlocks.get(floorKey);
                if (floorBlock && floorBlock.type !== 'air') {
                    hasFloor = true;
                }
            }
            if (!hasFloor) {
                mob.vx = 0; mob.vz = 0; mob.aiState.timer = 0; return;
            }

            // 3. Auto Jump (WITH ROOF GLITCH FIX)
            // If we are sleeping and hit a house wall (sand/stone/wood), DO NOT JUMP.
            // This forces them to slide along the wall until they find the door.
            const isHouseBlock = wallBlock && (wallBlock.type === 'sand' || wallBlock.type === 'wood');
            const preventJump = mob.aiState.mode === 'sleeping' && isHouseBlock;

            if (wallBlock && wallBlock.type !== 'air' && wallBlock.type !== 'crop' && !wallBlock.type.includes('door')) {
                 if (!preventJump) {
                     // Server vs Client Velocity
                     if (mob.vy !== undefined && mob.vy === 0) mob.vy = 25;
                     if (mob.velocity && mob.velocity.y === 0) mob.velocity.y = 25;
                 }
            }

        } else {
            // Arrived
            if (mob.vx !== undefined) { mob.vx = 0; mob.vz = 0; }
            else { mob.velocity.x = 0; mob.velocity.z = 0; }
            
            if (mob.aiState.mode === 'farming') {
                if(mob.yaw !== undefined) mob.yaw += delta * 2;
                else mob.mesh.rotation.y += delta * 2;
            }
        }
    }
}

// --- HELPER: Check if a location is "Indoors" (Has a solid block above it) ---
function isLocationIndoors(x, y, z, dim) {
    const bx = Math.round(x / BLOCK_SIZE) * BLOCK_SIZE;
    const bz = Math.round(z / BLOCK_SIZE) * BLOCK_SIZE;
    const startY = Math.round(y / BLOCK_SIZE) * BLOCK_SIZE;

    // Scan 5 blocks up. If we hit a solid block (stone, wood, etc), it's a house/cave.
    // We ignore leaves so they still attack under trees.
    for(let i = 1; i <= 5; i++) {
        const checkY = startY + (i * BLOCK_SIZE);
        const k = getKey(bx, checkY, bz, dim);
        const block = worldBlocks.get(k);
        if (block && block.type !== 'air' && block.type !== 'leaves' && block.type !== 'barrier') {
            return true; // Found a roof
        }
    }
    return false;
}

function updateMobs(delta) {
    const prevTimeRatio = (worldTime % DAY_DURATION) / DAY_DURATION;
    worldTime += delta;
    if (worldTime >= DAY_DURATION) worldTime = 0;
    const timeRatio = (worldTime % DAY_DURATION) / DAY_DURATION;

    if (prevTimeRatio > 0.99 && timeRatio < 0.05) {
        let hasDoor = false;
        worldBlocks.forEach((b, k) => {
            if (!hasDoor && (b.type === 'door' || b.type === 'mysterious_door')) {
                const parts = k.split(',');
                const dist = Math.hypot(parseInt(parts[0]) - 300, parseInt(parts[2]) - 0);
                if (dist < 200) hasDoor = true;
            }
        });
        
        if (hasDoor && global.villageInitialCap) {
            const vCount = mobs.filter(m => m.type === 'villager' && !m.isDead && m.dim === 'overworld').length;
            const toSpawn = global.villageInitialCap - vCount;
            for (let i = 0; i < toSpawn; i++) {
                spawnMob('villager', 300 + (Math.random()-0.5)*100, 10, (Math.random()-0.5)*100, 'overworld');
            }
        }
    }

    attemptNaturalMobSpawning();

    const activePlayers = Array.from(players.values());
    const survivalPlayers = activePlayers.filter(p => p.mode === 'survival' && p.health > 0);
    const aliveMobs = mobs.filter(m => !m.isDead);

    // ... (Player hazard check code) ...
    activePlayers.forEach(p => {
        if (p.mode === 'survival') {
            if (checkHazardDamage(p)) {
                const client = getClientById(p.id);
                if (client) client.send(JSON.stringify({ type: 'damage', health: p.health }));
                if (p.health <= 0) {
                    if (p.in2FAFlow) fail2FAServer(p);
                    else {
                        p.health = 20;
                        p.x=0; p.y=60; p.z=0;
                        if (client) client.send(JSON.stringify({ type: 'respawn', x:0, y:60, z:0 }));
                    }
                }
            }
        }
    });

    // Update Projectiles
    for (let i = projectiles.length - 1; i >= 0; i--) {
        const p = projectiles[i];
        p.life -= delta;
        p.x += p.vx * delta;
        p.y += p.vy * delta;
        p.z += p.vz * delta;

        // Collision Check (Simplified: Check players & blocks)
        let hit = false;

        // 1. Block Collision
        const bx = Math.round(p.x/5)*5; const by = Math.round(p.y/5)*5; const bz = Math.round(p.z/5)*5;
        const k = getKey(bx, by, bz, p.dim);
        const b = worldBlocks.get(k);
        if (b && b.type !== 'air' && b.type !== 'water' && b.type !== 'lava' && b.type !== 'crop') {
            hit = true;
            // Fire logic could go here (set block on fire)
        }

        // 2. Player Collision
        if (!hit) {
            survivalPlayers.forEach(pl => {
                if (pl.dim === p.dim) {
                    const dist = Math.hypot(p.x - pl.x, p.y - (pl.y+3), p.z - pl.z); // Center mass
                    if (dist < 4) {
                        hit = true;
                        if (!damagePlayerInBattle(pl, 5)) {
                            pl.health -= 5; // 2.5 Hearts
                            const client = getClientById(pl.id);
                            if (client) client.send(JSON.stringify({ type: 'damage', health: pl.health }));
                            if (pl.health <= 0) {
                                if (pl.in2FAFlow) fail2FAServer(pl);
                                else {
                                    pl.health = 20; pl.x=0; pl.y=60; pl.z=0;
                                    if (client) client.send(JSON.stringify({ type: 'respawn', x:0, y:60, z:0 }));
                                }
                            }
                        }
                    }
                }
            });
        }

        if (hit || p.life <= 0) {
            projectiles.splice(i, 1);
        }
    }

    aliveMobs.forEach(mob => {
        if (mob.type === 'end_crystal') return;

        if (mob.type === 'scc') {
            mob.vx = 0; mob.vy = 0; mob.vz = 0;
            return;
        }

        // --- ULTRA-FAST PATH FOR TORK ---
        if (mob.type === 'tork') {
            mob.vx = 0; mob.vy = 0; mob.vz = 0;
            if (!mob.tradingWith) {
                mob.yaw += (Math.random() - 0.5) * delta;
                mob.lookAt = { x: mob.x + Math.sin(mob.yaw), y: mob.y, z: mob.z + Math.cos(mob.yaw) };
            }
            return;
        }

        if (mob.type === 'queen' && mob.queenEncounter && (!mob.battle || !mob.battle.active)) {
            survivalPlayers.forEach(p => {
                if (p.dim === mob.dim) {
                    const dist = Math.hypot(p.x - mob.x, p.z - mob.z);
                    if (dist < 40) {
                        mob.queenEncounter = false;
                        const client = getClientById(p.id);
                        if (client) {
                            client.send(JSON.stringify({ type: 'deltarune_text', text: [
                                "* Oh My God It Is The Lightners",
                                "* I Am Queen (Q5U4EX7YY2E9N)",
                                "* I Only Play Mobile Games",
                                "* Prepare To Be Captured And/Or Entertained"
                            ]}));
                            setTimeout(() => { if (!mob.isDead) startDeltaruneBattle(mob, p); }, 8000);
                        }
                    }
                }
            });
        }

        if (mob.type === 'tenna' && mob.tennaEncounter) {
            survivalPlayers.forEach(p => {
                if (p.dim === mob.dim) {
                    const dist = Math.hypot(p.x - mob.x, p.z - mob.z);
                    if (dist < 40) {
                        mob.tennaEncounter = false;
                        const client = getClientById(p.id);
                        if (client) {
                            client.send(JSON.stringify({ type: 'deltarune_text', text: [
                                "* WELCOME TO THE SHOW, LIGHTNERS!",
                                "* DON'T TOUCH THAT DIAL!",
                                "* LET'S PLAY A GAME!",
                                "* IT'S TV TIME!"
                            ]}));
                            setTimeout(() => { client.send(JSON.stringify({type: 'start_ch3_minigame'})); }, 6000);
                        }
                    }
                }
            });
        }
        
        if (mob.type === 'titan' && mob.titanEncounter && (!mob.battle || !mob.battle.active)) {
            survivalPlayers.forEach(p => {
                if (p.dim === mob.dim) {
                    const dist = Math.hypot(p.x - mob.x, p.z - mob.z);
                    if (dist < 40) {
                        mob.titanEncounter = false;
                        const client = getClientById(p.id);
                        if (client) {
                            client.send(JSON.stringify({ type: 'deltarune_text', text: [
                                "* The Roaring has begun.",
                                "* Face the Titan."
                            ]}));
                            setTimeout(() => { if (!mob.isDead) startDeltaruneBattle(mob, p); }, 4000);
                        }
                    }
                }
            });
        }

        if (mob.type === 'lancer' && mob.lancerEncounter && (!mob.battle || !mob.battle.active)) {
            survivalPlayers.forEach(p => {
                if (p.dim === mob.dim) {
                    const dist = Math.hypot(p.x - mob.x, p.z - mob.z);
                    if (dist < 40) {
                        mob.lancerEncounter = false;
                        const client = getClientById(p.id);
                        if (client) {
                            client.send(JSON.stringify({ type: 'deltarune_text', text: [
                                "* Ho ho ho! The darkeners are ready!",
                                "* I am Lancer!",
                                "* Prepare to be thrashed!"
                            ]}));
                            // Start battle automatically after giving the player 6 seconds to read
                            setTimeout(() => { if (!mob.isDead) startDeltaruneBattle(mob, p); }, 6000);
                        }
                    }
                }
            });
        }

        // --- BATTLE STATE MACHINE ---
        if (mob.battle && mob.battle.active) {
            mob.battle.timer -= delta;
            
            const battlePlayer = players.get(mob.battle.playerId);
            const client = getClientById(mob.battle.playerId);

            if (mob.battle.state === 'player_action_realtime') {
                if (mob.battle.timer <= 0) {
                    mob.battle.state = 'enemy_turn_realtime';
                    mob.battle.vulnerable = false;
                    mob.battle.timer = 7.0; // 7 seconds to dodge
                    if (client) client.send(JSON.stringify({ type: 'battle_state', state: 'enemy_turn_realtime' }));
                }
            } else if (mob.battle.state === 'enemy_turn_realtime') {
                if (mob.battle.timer <= 0) {
                    mob.battle.state = 'menu';
                    sendBattleState(battlePlayer, mob, 'menu');
                } else {
                    // DODGE PHASE ENEMY AI
                    if ((mob.type === 'lancer' || mob.type === 'queen' || mob.type === 'titan') && battlePlayer) {
                        mob.lookAt = { x: battlePlayer.x, y: mob.y, z: battlePlayer.z };
                        mob.shotTimer = (mob.shotTimer || 0) + delta;
                        
                        mob.vx = Math.sin(worldTime * 3) * 10;
                        mob.vz = Math.cos(worldTime * 2) * 5;

                        let fireRate = mob.type === 'lancer' ? 0.8 : (mob.type === 'queen' ? 0.4 : 0.6);
                        
                        if (mob.shotTimer > fireRate) {
                            mob.shotTimer = 0;
                            const dx = battlePlayer.x - mob.x;
                            const dy = (battlePlayer.y + 3) - (mob.y + 2);
                            const dz = battlePlayer.z - mob.z;
                            const len = Math.hypot(dx, dy, dz);
                            const speed = mob.type === 'queen' ? 30 : 18; 
                            
                            projectiles.push({
                                id: Math.random().toString(36).substr(2, 9),
                                x: mob.x, y: mob.y + 2, z: mob.z,
                                vx: (dx/len) * speed + (Math.random()-0.5)*5, vy: (dy/len) * speed, vz: (dz/len) * speed + (Math.random()-0.5)*5,
                                dim: mob.dim, ownerId: mob.id, life: 5.0
                            });
                        }
                    }
                }
            }
            
            // Standard Physics while in battle (friction + gravity)
            mob.vx *= 0.8; mob.vz *= 0.8;
            mob.vy -= 9.8 * 50.0 * delta;
            
            let groundY = -601;
            const bx = Math.round(mob.x/5)*5; const bz = Math.round(mob.z/5)*5;
            for(let y=Math.floor(mob.y/5)*5; y>-600; y-=5) {
                const kKey = getKey(bx,y,bz,mob.dim);
                const blockData = worldBlocks.get(kKey);
                if (blockData && blockData.type !== 'air' && blockData.type !== 'water') { groundY = y + 5; break; }
            }
            if (mob.y + mob.vy * delta < groundY) { mob.y = groundY; mob.vy = 0; }
            else { mob.y += mob.vy * delta; }
            mob.x += mob.vx * delta; mob.z += mob.vz * delta;
            
            return; // Skip standard AI below
        }

        // --- OWCA & RALSEI AI ---
        if (mob.type === 'owca' || (mob.type === 'ralsei' && mob.inParty)) {
            const owner = players.get(mob.ownerId);
            if (owner && owner.dim === mob.dim) {
                const dist = Math.hypot(mob.x - owner.x, mob.y - owner.y, mob.z - owner.z);
                if (dist > 200) {
                    const angle = owner.yaw + Math.PI;
                    mob.x = owner.x + Math.sin(angle) * 30;
                    mob.z = owner.z + Math.cos(angle) * 30;
                    mob.y = owner.y + 20;
                    broadcast({ type: 'spawner_particles', x: mob.x, y: mob.y, z: mob.z, dim: mob.dim });
                } else if (dist > 15) {
                    mob.lookAt = { x: owner.x, y: mob.y, z: owner.z };
                    const flatDist = Math.hypot(owner.x - mob.x, owner.z - mob.z);
                    if (flatDist > 0) {
                        mob.vx = ((owner.x - mob.x)/flatDist) * 20;
                        mob.vz = ((owner.z - mob.z)/flatDist) * 20;
                        const nextX = mob.x + (mob.vx/20)*3; const nextZ = mob.z + (mob.vz/20)*3;
                        const k = getKey(Math.round(nextX/5)*5, Math.round(mob.y/5)*5, Math.round(nextZ/5)*5, mob.dim);
                        const block = worldBlocks.get(k);
                        if(block && block.type !== 'air' && block.type !== 'water' && mob.vy === 0) mob.vy = 25;
                    }
                } else {
                    mob.lookAt = { x: owner.x, y: mob.y, z: owner.z };
                    mob.vx *= 0.8; mob.vz *= 0.8;
                }
            }
            
            mob.vy -= 9.8 * 50.0 * delta;
            let groundY = -601;
            const bx = Math.round(mob.x/5)*5; const bz = Math.round(mob.z/5)*5;
            for(let y=Math.floor(mob.y/5)*5; y>-600; y-=5) {
                const kKey = getKey(bx,y,bz,mob.dim);
                const blockData = worldBlocks.get(kKey);
                if (blockData && blockData.type !== 'air' && blockData.type !== 'water') { groundY = y + 5; break; }
            }
            if (mob.y + mob.vy * delta < groundY) { mob.y = groundY; mob.vy = 0; }
            else { mob.y += mob.vy * delta; }
            mob.x += mob.vx * delta; mob.z += mob.vz * delta;

            if (checkHazardDamage(mob)) { /* normal damage processes */ }
            if (mob.isDead) {
                mob.health = 30; mob.isDead = false;
                mob.x += 10000;
            }
            return;
        }

        // --- ULTRA-FAST PATH FOR MERCHANTS ---
        if (mob.type === 'merchant') {
            mob.vx = 0; mob.vy = 0; mob.vz = 0;
            const isMarketNight = timeRatio >= 0.4 && timeRatio < 0.95;
            if (isMarketNight && !mob.isInvisible) {
                mob.isInvisible = true;
                broadcast({ type: 'spawner_particles', x: mob.x, y: mob.y + 3, z: mob.z, dim: mob.dim });
            } else if (!isMarketNight && mob.isInvisible) {
                mob.isInvisible = false;
                broadcast({ type: 'spawner_particles', x: mob.x, y: mob.y + 3, z: mob.z, dim: mob.dim });
            }

            if (!mob.tradingWith && !mob.isInvisible) {
                mob.yaw += (Math.random() - 0.5) * delta;
                mob.lookAt = { x: mob.x + Math.sin(mob.yaw), y: mob.y, z: mob.z + Math.cos(mob.yaw) };
            }
            return; // Skip heavy physics, raycasts, gravity, and AI
        }

        // --- VOIDLING AI & VARIANTS ---
        if (mob.type.startsWith('void')) {
            checkHazardDamage(mob); 
            if (mob.isDead) return;

            let targetP = null; let minD = 100;
            survivalPlayers.forEach(p => {
                if (p.dim === mob.dim) {
                    const d = Math.hypot(p.x - mob.x, p.z - mob.z);
                    if (d < minD) { minD = d; targetP = p; }
                }
            });

            if (!mob.phase) mob.phase = mob.type === 'void_behemoth' ? 'lumbering' : 'stalking';
            if (mob.phaseTimer === undefined) mob.phaseTimer = 0;
            mob.phaseTimer += delta;

            let groundY = -1000;
            const bx = Math.round(mob.x/5)*5; const bz = Math.round(mob.z/5)*5;
            for(let y=Math.floor(mob.y/5)*5 + 10; y>-600; y-=5) {
                const b = worldBlocks.get(getKey(bx,y,bz,mob.dim));
                if(b && b.type !== 'air' && b.type !== 'water' && b.type !== 'lava') { groundY = y + 5; break; }
            }

            const isMarket = mob.x > 40000 && mob.z > 40000;
            const isSunrise = timeRatio >= 0.9 && timeRatio < 0.99;

            if (isMarket && isSunrise) {
                mob.phase = 'diving';
                mob.vy = -200; 
                if (mob.y < groundY - 15) {
                    mob.isDead = true;
                    createVoidExplosion(mob.x, mob.y, mob.z, mob.dim);
                    broadcast({ type: 'entity_update', mob });
                    return;
                }
            } else if (targetP) {
                mob.lookAt = { x: targetP.x, y: mob.y, z: targetP.z };
                const dx = targetP.x - mob.x;
                const dz = targetP.z - mob.z;
                const len = Math.hypot(dx, dz);
                const isAuth = targetP.authenticated;

                if (mob.type === 'voidling') {
                    mob.vx *= 0.8; mob.vz *= 0.8;
                    if (mob.phase === 'stalking') {
                        mob.vy = (groundY + 10 - mob.y) * 2;
                        if (len > 0) { mob.vx += (dx/len) * 20 * delta; mob.vz += (dz/len) * 20 * delta; }
                        if (minD < 20 && mob.phaseTimer > 4) { mob.phase = 'diving'; mob.phaseTimer = 0; }
                    } else if (mob.phase === 'diving') {
                        mob.vy = (groundY - 5 - mob.y) * 5; 
                        if (len > 0) { mob.vx += (dx/len) * 150 * delta; mob.vz += (dz/len) * 150 * delta; }
                        if (minD < 4) { mob.phase = 'striking'; mob.phaseTimer = 0; } 
                        else if (mob.phaseTimer > 3) { mob.phase = 'stalking'; mob.phaseTimer = 0; }
                    } else if (mob.phase === 'striking') {
                        mob.vy = 80;
                        if (mob.phaseTimer > 0.2) {
                            if (minD < 8) {
                                targetP.health -= isAuth ? 3 : 15;
                                const client = getClientById(targetP.id);
                                if (client) client.send(JSON.stringify({ type: 'damage', health: targetP.health }));
                                if (targetP.health <= 0) {
                                    if (targetP.in2FAFlow) fail2FAServer(targetP);
                                    else { targetP.health = 20; targetP.x = 0; targetP.y = 60; targetP.z = 0; if (client) client.send(JSON.stringify({ type: 'respawn', x:0, y:60, z:0 })); }
                                }
                            }
                            mob.phase = 'stalking'; mob.phaseTimer = -2;
                        }
                    }
                } else if (mob.type === 'void_weaver') {
                    mob.vx *= 0.8; mob.vz *= 0.8;
                    if (mob.phase === 'stalking') {
                        mob.vy = (groundY + 15 - mob.y) * 2;
                        if (len > 0) { mob.vx += (dx/len) * 15 * delta; mob.vz += (dz/len) * 15 * delta; }
                        if (minD < 25 && mob.phaseTimer > 3) { mob.phase = 'channeling'; mob.phaseTimer = 0; }
                    } else if (mob.phase === 'channeling') {
                        mob.vy = (groundY + 15 - mob.y) * 2;
                        mob.vx = 0; mob.vz = 0;
                        if (len > 0) {
                            const pullStrength = isAuth ? 20 : 80;
                            targetP.x -= (dx/len) * pullStrength * delta;
                            targetP.z -= (dz/len) * pullStrength * delta;
                            const client = getClientById(targetP.id);
                            if (client) client.send(JSON.stringify({ type: 'knockback', vx: -(dx/len)*pullStrength, vy: 0, vz: -(dz/len)*pullStrength }));
                        }
                        if (mob.phaseTimer > 2) { mob.phase = 'striking'; mob.phaseTimer = 0; }
                    } else if (mob.phase === 'striking') {
                        mob.vy = -100;
                        if (mob.y <= groundY + 5) {
                            if (minD < 6) {
                                targetP.health -= isAuth ? 2 : 10;
                                const client = getClientById(targetP.id);
                                if (client) client.send(JSON.stringify({ type: 'damage', health: targetP.health }));
                                if (targetP.health <= 0) {
                                    if (targetP.in2FAFlow) fail2FAServer(targetP);
                                    else { targetP.health = 20; targetP.x = 0; targetP.y = 60; targetP.z = 0; if (client) client.send(JSON.stringify({ type: 'respawn', x:0, y:60, z:0 })); }
                                }
                            }
                            mob.phase = 'stalking'; mob.phaseTimer = -2;
                        }
                    }
                } else if (mob.type === 'void_behemoth') {
                    if (mob.phase === 'lumbering') {
                        mob.vy -= 9.8 * 50 * delta;
                        if (mob.y + mob.vy * delta < groundY) { mob.y = groundY; mob.vy = 0; }
                        if (len > 0 && mob.y <= groundY + 1) { mob.vx = (dx/len) * 5; mob.vz = (dz/len) * 5; }
                        else { mob.vx *= 0.9; mob.vz *= 0.9; }
                        if (minD < 15 && mob.phaseTimer > 4 && mob.y <= groundY + 1) { mob.phase = 'leaping'; mob.phaseTimer = 0; }
                    } else if (mob.phase === 'leaping') {
                        mob.vy = 60;
                        if (len > 0) { mob.vx = (dx/len) * 20; mob.vz = (dz/len) * 20; }
                        mob.phase = 'airborne';
                    } else if (mob.phase === 'airborne') {
                        mob.vy -= 9.8 * 50 * delta;
                        if (mob.y + mob.vy * delta < groundY) {
                            mob.y = groundY; mob.vy = 0; mob.vx = 0; mob.vz = 0;
                            mob.phase = 'crashing'; mob.phaseTimer = 0;
                        }
                    } else if (mob.phase === 'crashing') {
                        createExplosion(mob.x, mob.y, mob.z, mob.dim, 3);
                        survivalPlayers.forEach(p => {
                            if (p.dim === mob.dim) {
                                const dist = Math.hypot(p.x - mob.x, p.z - mob.z);
                                if (dist < 15 && p.y < groundY + 10) {
                                    p.health -= p.authenticated ? 5 : 25;
                                    const client = getClientById(p.id);
                                    if (client) {
                                        client.send(JSON.stringify({ type: 'damage', health: p.health }));
                                        client.send(JSON.stringify({ type: 'knockback', vx: 0, vy: 600, vz: 0 }));
                                    }
                                    if (p.health <= 0) {
                                        if (p.in2FAFlow) fail2FAServer(p);
                                        else { p.health = 20; p.x = 0; p.y = 60; p.z = 0; if (client) client.send(JSON.stringify({ type: 'respawn', x:0, y:60, z:0 })); }
                                    }
                                }
                            }
                        });
                        mob.phase = 'lumbering'; mob.phaseTimer = -2;
                    }
                }
            } else {
                mob.phase = mob.type === 'void_behemoth' ? 'lumbering' : 'stalking';
                if (mob.type === 'voidling') mob.vy = (groundY + 10 - mob.y) * 2;
                else if (mob.type === 'void_weaver') mob.vy = (groundY + 15 - mob.y) * 2;
                else if (mob.type === 'void_behemoth') mob.vy -= 9.8 * 50 * delta;
                
                if (mob.type === 'void_behemoth' && mob.y + mob.vy * delta < groundY) { mob.y = groundY; mob.vy = 0; }
                
                mob.vx *= 0.8; mob.vz *= 0.8;
                mob.lookAt = { x: mob.x + 10, y: mob.y, z: mob.z };
            }

            mob.x += mob.vx * delta;
            mob.y += Math.max(-200, Math.min(200, mob.vy)) * delta;
            mob.z += mob.vz * delta;
            if (mob.y < -600) mob.isDead = true;
            return;
        }

        // --- SULFUR CUBE PHYSICS & AI ---
        if (mob.type === 'sulfur_cube') {
            let grav = 50.0;
            let fricX = 0.9; let fricZ = 0.9;
            let bounce = 0;
            let speed = 15;
            
            if (mob.archetype === 'bouncy') { bounce = 0.8; fricX = 0.95; fricZ = 0.95; speed = 30; }
            if (mob.archetype === 'sliding') { fricX = 0.99; fricZ = 0.99; speed = 5; }
            if (mob.archetype === 'floating') { grav = 5.0; speed = 10; }
            if (mob.archetype === 'sticky') { fricX = 0.5; fricZ = 0.5; speed = 5; }
            if (mob.archetype === 'heavy') { grav = 100.0; fricX = 0.7; fricZ = 0.7; speed = 8; }
            
            if (mob.archetype === 'explosive') {
                mob.explodeTimer += delta;
                if (mob.explodeTimer > 3.0) {
                    mob.isDead = true;
                    broadcast({ type: 'entity_update', mob: mob });
                    createExplosion(mob.x, mob.y, mob.z, mob.dim, 5);
                    return;
                }
            }

            // Random wander AI (only if empty)
            if (!mob.eatenBlock) {
                mob.aiState.timer -= delta;
                if (mob.aiState.timer <= 0) {
                    mob.aiState.timer = 2 + Math.random() * 5;
                    mob.aiState.target = { x: mob.x + (Math.random()-0.5)*40, z: mob.z + (Math.random()-0.5)*40 };
                }

                if (mob.aiState.target) {
                    const dx = mob.aiState.target.x - mob.x;
                    const dz = mob.aiState.target.z - mob.z;
                    const len = Math.hypot(dx, dz);
                    if (len > 1) {
                        mob.vx += (dx/len) * speed * delta * 10;
                        mob.vz += (dz/len) * speed * delta * 10;
                    }
                }
            } else {
                mob.aiState.target = null; // Lose AI when holding a block
            }

            mob.vy -= 9.8 * grav * delta;
            mob.vx *= fricX;
            mob.vz *= fricZ;

            // Ground check
            let groundY = -1000;
            const bpx = Math.round(mob.x/5)*5;
            const bpz = Math.round(mob.z/5)*5;
            for(let y=Math.floor(mob.y/5)*5; y>-600; y-=5) {
                const b = worldBlocks.get(getKey(bpx,y,bpz,mob.dim));
                if(b && b.type !== 'air' && b.type !== 'water' && b.type !== 'lava') { 
                    groundY = y + 5; break; 
                }
            }

            if (mob.y + mob.vy * delta < groundY) {
                if (bounce > 0 && Math.abs(mob.vy) > 10) {
                    mob.vy = Math.abs(mob.vy) * bounce;
                } else {
                    mob.vy = 0;
                    if (Math.random() < 0.05 && speed > 5) mob.vy = (mob.archetype === 'bouncy' ? 50 : 20);
                }
                mob.y = groundY;
            } else {
                mob.y += mob.vy * delta;
            }

            mob.x += mob.vx * delta;
            mob.z += mob.vz * delta;
            if (mob.aiState.target) { mob.lookAt = { x: mob.aiState.target.x, y: mob.y, z: mob.aiState.target.z }; }
            
            if (mob.y < -600) mob.isDead = true;
            return;
        }
        
        // Blaze Fly/Hover Logic
        if (mob.type === 'blaze') {
             // Friction
             mob.vx *= 0.95; mob.vz *= 0.95; mob.vy *= 0.95;
             
             // Bob up and down
             mob.vy += Math.sin(worldTime * 2) * 2.0; 
             
             // Keep height from ground
             let groundY = -100;
             const bx = Math.round(mob.x/5)*5; const bz = Math.round(mob.z/5)*5;
             for(let y=Math.floor(mob.y/5)*5; y > -50; y-=5) {
                  const k = getKey(bx,y,bz,mob.dim);
                  const b = worldBlocks.get(k);
                  if(b && b.type !== 'air') { groundY = y + 5; break; }
             }
             if (mob.y < groundY + 10) mob.vy += 20 * delta; // Fly up
             
             // Update LookAt for Blaze (Face nearest player)
             let closestP = null; let minD = 999;
             survivalPlayers.forEach(p => {
                 if (p.dim === mob.dim) {
                     const d = Math.hypot(p.x-mob.x, p.y-p.y, p.z-mob.z);
                     // Line of Sight simplified to distance for performance (48 blocks aggro)
                     if(d < 48 && d < minD) { minD = d; closestP = p; }
                 }
             });

             if (closestP) {
                 mob.lookAt = { x: closestP.x, y: closestP.y, z: closestP.z };
                 
                 // --- BLAZE COMBAT AI ---
                 // 1. Charge Up (3 Seconds)
                 if (!mob.isCharging && mob.chargeTick >= 0) {
                     mob.chargeTick += delta;
                     if (mob.chargeTick > 3.0) {
                         mob.isCharging = true;
                         mob.shotsFired = 0;
                         mob.shotTimer = 0;
                     }
                 }

                 // 2. Firing (Burst of 3)
                 if (mob.isCharging) {
                     mob.shotTimer += delta;
                     if (mob.shotTimer > 0.15) { // Time between individual shots
                         mob.shotTimer = 0;
                         mob.shotsFired++;
                         
                         // Calculate aim vector
                         const dx = closestP.x - mob.x;
                         const dy = (closestP.y + 3) - (mob.y + 4); // Aim at head/upper body
                         const dz = closestP.z - mob.z;
                         const len = Math.hypot(dx, dy, dz);
                         const speed = 40; // Fast fireball
                         
                         // Add projectile
                         projectiles.push({
                             id: Math.random().toString(36).substr(2, 9),
                             x: mob.x, y: mob.y + 4, z: mob.z, // Fire from rods height
                             vx: (dx/len) * speed + (Math.random()-0.5)*2, // Slight inaccuracy
                             vy: (dy/len) * speed + (Math.random()-0.5)*2,
                             vz: (dz/len) * speed + (Math.random()-0.5)*2,
                             dim: mob.dim,
                             ownerId: mob.id,
                             life: 5.0 // 5 seconds max life
                         });

                         if (mob.shotsFired >= 3) {
                             mob.isCharging = false;
                             mob.chargeTick = -2.0; // 2 Second Cooldown before charging again
                         }
                     }
                 }
                 
                 // Cooldown recovery
                 if (mob.chargeTick < 0) mob.chargeTick += delta;

             } else {
                 // Look forward if no player
                 mob.lookAt = { x: mob.x + 10, y: mob.y, z: mob.z };
                 mob.isCharging = false;
                 if (mob.chargeTick > 0) mob.chargeTick -= delta; // Decay charge if player lost
             }

             mob.x += mob.vx * delta;
             mob.y += mob.vy * delta;
             mob.z += mob.vz * delta;
             return; 
        }

        // --- NEW: ENTITY PORTAL LOGIC ---
        if (!mob.lastPortalTime) mob.lastPortalTime = 0;
        const now = performance.now();

        if (now - mob.lastPortalTime > 3000) {
            const bx = Math.round(mob.x / BLOCK_SIZE) * BLOCK_SIZE;
            const by = Math.round(mob.y / BLOCK_SIZE) * BLOCK_SIZE;
            const bz = Math.round(mob.z / BLOCK_SIZE) * BLOCK_SIZE;
            const key = getKey(bx, by, bz, mob.dim);
            const block = worldBlocks.get(key);

            if (block && (block.type === 'portal' || block.type === 'nether_portal')) {
                // Switch Dimension
                let newDim = 'overworld';
                let dest = {x:0, y:60, z:0};

                if (block.type === 'portal') {
                    newDim = (mob.dim === 'overworld') ? 'the_end' : 'overworld';
                    dest = {x:0, y:60, z:0};
                }
                if (block.type === 'nether_portal') {
                    newDim = (mob.dim === 'overworld') ? 'the_nether' : 'overworld';
                    dest = findOrGeneratePortal(mob.x, mob.y, mob.z, newDim);
                }
                
                mob.dim = newDim;
                mob.x = dest.x; mob.y = dest.y; mob.z = dest.z; 
                mob.vx = 0; mob.vz = 0;
                mob.lastPortalTime = now;
                broadcast({ type: 'entity_update', mob: mob });
            }
        }

        // --- NEW: Update Villager AI ---
        if (mob.type === 'villager' || mob.type === 'mercator') updateVillagerAI(mob, delta, timeRatio);

        if (checkHazardDamage(mob)) {
            if (mob.health <= 0) {
                mob.isDead = true;
                broadcast({ type: 'entity_update', mob: mob });
            } else {
                broadcast({ type: 'entity_update', mob: mob });
            }
        }

        // --- ZOMBIE SUNLIGHT BURNING ---
        // Day is roughly 0.0 to 0.4 and 0.9 to 1.0. Night is 0.45 to 0.9.
        const isDay = timeRatio < 0.45 || timeRatio > 0.95;
        const isTaiga = mob.x < -600;
        if (isDay && !isTaiga && (mob.type === 'zombie' || mob.type === 'diddy') && mob.naturalSpawn && mob.dim === 'overworld') {
            // Check if under open sky
            if (isExposedToSun(mob.x, mob.y, mob.z, mob.dim)) {
                const now = performance.now();
                // Burn damage every 0.5 seconds
                if (now - (mob.lastDamageTime || 0) > 500) {
                    mob.health--;
                    mob.lastDamageTime = now;
                    if (mob.health <= 0) mob.isDead = true;
                    broadcast({ type: 'entity_update', mob: mob });
                }
            }
        }

        mob.vy -= 9.8 * 50.0 * delta;
        
        let groundY = -601;
        const bx = Math.round(mob.x/5)*5;
        const bz = Math.round(mob.z/5)*5;

        const isTaigaCave = mob.x < -600 && mob.y < 30 && mob.dim === 'overworld';
        const isMarket = mob.x > 40000 && mob.z > 40000 && mob.dim === 'overworld';
        
        if ((isTaigaCave || isMarket) && mob.vy > 0) {
             const ceilY = Math.floor(mob.y/5)*5 + 5;
             const cb = worldBlocks.get(getKey(bx, ceilY, bz, mob.dim));
             if (cb && cb.type !== 'air' && !cb.type.includes('door')) {
                 mob.vy = 0;
             }
        }

        for(let y=Math.floor(mob.y/5)*5; y>-600; y-=5) {
             const kKey = getKey(bx,y,bz,mob.dim);
             const blockData = worldBlocks.get(kKey);
             if (blockData && blockData.type !== 'air' && blockData.type !== 'crop' && blockData.type !== 'water') {
                 if ((isTaigaCave || isMarket) && y > mob.y - 5) {
                     // Prevent clipping to roof
                 } else {
                     groundY = y + 5; 
                     break;
                 }
             }
        }

        if (mob.y + mob.vy * delta < groundY) {
            mob.y = groundY;
            mob.vy = 0;
        } else {
            mob.y += mob.vy * delta;
        }

        mob.x += mob.vx * delta;
        mob.z += mob.vz * delta;

        // --- MOB AI ---
        let target = null;
        let minDist = 80; 
        let victim = null;
        let isPlayer = false;

        // PIGMAN AGGRO CHECK
        if (mob.type === 'pigman') {
            if (mob.aiState.mode === 'aggressive' && mob.aiState.targetId) {
                const p = players.get(mob.aiState.targetId);
                // Check if target is valid, alive, in same dim, and survival
                if (p && p.dim === mob.dim && p.mode === 'survival' && p.health > 0) {
                    const dist = Math.hypot(mob.x - p.x, mob.y - p.y, mob.z - p.z);
                    if (dist < 80) { // Aggro range
                        minDist = dist;
                        target = { x: p.x, y: p.y, z: p.z };
                        victim = p;
                        isPlayer = true;
                    }
                } else {
                    mob.aiState.mode = 'idle'; // Target lost
                }
            }
        }

        if (mob.type === 'lynx') {
            aliveMobs.forEach(other => {
                if ((other.type === 'zombie' || other.type === 'diddy') && other.dim === mob.dim) {
                    const dist = Math.hypot(mob.x-other.x, mob.y-other.y, mob.z-other.z);
                    if (dist < minDist && dist < 20 * BLOCK_SIZE) { 
                        minDist = dist; target = {x: other.x, y: other.y, z: other.z}; victim = other; isPlayer = false; 
                    }
                }
            });
            if (!target) {
                mob.aiState.timer -= delta;
                if (mob.aiState.timer <= 0) {
                    mob.aiState.timer = 2 + Math.random() * 4;
                    mob.aiState.target = { x: mob.x + (Math.random() - 0.5) * 40, z: mob.z + (Math.random() - 0.5) * 40 };
                }
                if (mob.aiState.target) target = mob.aiState.target;
            }
        } else if (mob.type === 'zombie' || mob.type === 'diddy' || mob.type === 'frostbound') {
            // 1. PANIC CHECK: Am I stuck inside a house?
            // If the zombie is under a roof, forced glitch-out (Reverse velocity violently)
            if (Math.random() < 0.1 && isLocationIndoors(mob.x, mob.y, mob.z, mob.dim)) {
                 mob.vx = (Math.random() - 0.5) * 30; // Random panic movement
                 mob.vz = (Math.random() - 0.5) * 30;
                 target = null; // Ignore targets while panicking
            } else {
                // Normal Targeting
                aliveMobs.forEach(other => {
                    if ((other.type === 'villager' || other.type === 'mercator' || other.type === 'lynx') && other.dim === mob.dim) {
                        const dist = Math.hypot(mob.x-other.x, mob.y-other.y, mob.z-other.z);
                        // NEW: Check if victim is safe indoors
                        if (dist < minDist && !isLocationIndoors(other.x, other.y, other.z, other.dim)) {
                            minDist = dist;
                            target = {x: other.x, y: other.y, z: other.z};
                            victim = other;
                            isPlayer = false;
                        }
                    }
                });

                survivalPlayers.forEach(p => {
                    if (p.dim === mob.dim) {
                        const dist = Math.hypot(mob.x-p.x, mob.y-p.y, mob.z-p.z);
                            // NEW: Check if player is safe indoors
                            if (dist < minDist && !isLocationIndoors(p.x, p.y, p.z, p.dim)) {
                            minDist = dist;
                            target = {x: p.x, y: p.y, z: p.z};
                            victim = p;
                            isPlayer = true;
                        }
                    }
                });

                }
        }

        // COMMON ATTACK LOGIC (Zombie, Pigman, Frostbound, Lynx)
        if (minDist < 8 && target && victim) {
            const now = performance.now();
            if (now - (mob.lastAttackTime || 0) > 1000) {
                let dmg = 1;
                if (mob.type === 'pigman') dmg = 3; 
                if (mob.type === 'diddy' || mob.type === 'frostbound') dmg = 2; 
                if (mob.type === 'lynx') dmg = 4; // Lynx hits hard against zombies

                mob.lastAttackTime = now;
                
                if (isPlayer) {
                    if (mob.type === 'frostbound') victim.immovableTimer = 2.0;
                    
                    const client = getClientById(victim.id);
                    if (mob.type === 'frostbound' && client) client.send(JSON.stringify({ type: 'status_sync', immovableTimer: victim.immovableTimer }));

                    if (!damagePlayerInBattle(victim, dmg)) {
                        victim.health -= dmg;
                        if (client) client.send(JSON.stringify({ type: 'damage', health: victim.health }));
                        
                        if (victim.health <= 0) {
                            if (victim.in2FAFlow) fail2FAServer(victim);
                            else {
                                victim.health = 20;
                                victim.x = 0; victim.y = 60; victim.z = 0; 
                                if (client) client.send(JSON.stringify({ type: 'respawn', x:0, y:60, z:0 }));
                            }
                        }
                    }
                } else {
                    victim.health -= dmg;
                    if (victim.health <= 0) victim.isDead = true;
                    broadcast({ type: 'entity_update', mob: victim });
                }
            }
            // Stop moving when attacking
            mob.vx = 0; mob.vz = 0;
        }

        // Apply Movement & Avoidance (Zombie & Pigman)
        const isKnockedBack = Math.abs(mob.vx) > 50 || Math.abs(mob.vz) > 50;
        if (target && (mob.type === 'zombie' || mob.type === 'pigman' || mob.type === 'diddy' || mob.type === 'frostbound' || mob.type === 'lynx') && !isKnockedBack) {
            mob.lookAt = {x: target.x, y: mob.y, z: target.z};
            const dx = target.x - mob.x;
            const dz = target.z - mob.z;
            const len = Math.hypot(dx, dz);
            if (len > 0.1) { 
                const speed = mob.type === 'lynx' ? 25 : (mob.type === 'frostbound' ? 12 : 15);
                mob.vx = (dx / len) * speed;
                mob.vz = (dz / len) * speed;

                // Simple Auto Jump
                const nextX = mob.x + (dx/len)*3; const nextZ = mob.z + (dz/len)*3;
                const k = getKey(Math.round(nextX/5)*5, Math.round(mob.y/5)*5, Math.round(nextZ/5)*5, mob.dim);
                const block = worldBlocks.get(k);
                
                const isClosedDoor = block && (block.type === 'door' || block.type === 'mysterious_door') && (!block.state || !block.state.open);
                if (isClosedDoor) {
                     mob.vx = 0; mob.vz = 0;
                } else if(block && block.type !== 'air' && block.type !== 'crop' && !block.type.includes('door') && block.type !== 'water') {
                     if(mob.vy === 0) mob.vy = 25;
                }
            }
        } else if (mob.type === 'zombie' || mob.type === 'pigman' || mob.type === 'diddy' || mob.type === 'frostbound' || mob.type === 'lynx') {
            // Friction
            if (isKnockedBack) {
                mob.vx -= mob.vx * 2.0 * delta;
                mob.vz -= mob.vz * 2.0 * delta;
            } else {
            mob.vx *= 0.9;
            mob.vz *= 0.9;
            }
        }

        if (mob.y < -600) mob.isDead = true;
    });
}

function checkNetherPortalServer(x, y, z, dim) {
    // Check neighbors to find potential frame start (bottom-left of air gap)
    for(let ox = x - 2*BLOCK_SIZE; ox <= x + 2*BLOCK_SIZE; ox += BLOCK_SIZE) {
        for(let oz = z - 2*BLOCK_SIZE; oz <= z + 2*BLOCK_SIZE; oz += BLOCK_SIZE) {
            for(let oy = y - 1*BLOCK_SIZE; oy <= y + 1*BLOCK_SIZE; oy += BLOCK_SIZE) {
                 if (checkFrame(ox, oy, oz, 1, 0, dim)) { fillNetherPortal(ox, oy, oz, 1, 0, dim); return; }
                 if (checkFrame(ox, oy, oz, 0, 1, dim)) { fillNetherPortal(ox, oy, oz, 0, 1, dim); return; }
            }
        }
    }
}

function checkFrame(x, y, z, dx, dz, dim) {
    const getKey = (bx, by, bz, d) => `${Math.round(bx)},${Math.round(by)},${Math.round(bz)},${d}`;
    // 2x3 Air
    for(let i=0; i<2; i++) {
        for(let j=0; j<3; j++) {
            const b = worldBlocks.get(getKey(x+(i*dx)*5, y+j*5, z+(i*dz)*5, dim));
            if (b && b.type !== 'air') return false;
        }
    }
    // Obsidian Frame
    for(let i=-1; i<3; i++) { // Top/Bottom
        const bb = worldBlocks.get(getKey(x+(i*dx)*5, y-5, z+(i*dz)*5, dim));
        const bt = worldBlocks.get(getKey(x+(i*dx)*5, y+15, z+(i*dz)*5, dim));
        if (!bb || bb.type !== 'obsidian') return false;
        if (!bt || bt.type !== 'obsidian') return false;
    }
    for(let j=0; j<3; j++) { // Sides
        const b1 = worldBlocks.get(getKey(x-dx*5, y+j*5, z-dz*5, dim));
        const b2 = worldBlocks.get(getKey(x+2*dx*5, y+j*5, z+2*dz*5, dim));
        if (!b1 || b1.type !== 'obsidian') return false;
        if (!b2 || b2.type !== 'obsidian') return false;
    }
    return true;
}

function fillNetherPortal(x, y, z, dx, dz, dim) {
    for(let i=0; i<2; i++) {
        for(let j=0; j<3; j++) {
            const px = x + (i*dx)*BLOCK_SIZE; const py = y + j*BLOCK_SIZE; const pz = z + (i*dz)*BLOCK_SIZE;
            addBlock(px, py, pz, 'nether_portal', dim);
            broadcast({ type: 'block_update', x: px, y: py, z: pz, blockType: 'nether_portal', dim });
        }
    }
}

// --- PORTAL LINKING SERVER SIDE ---
function findOrGeneratePortal(x, y, z, destDim) {
    const ratio = destDim === 'the_nether' ? 0.125 : 8;
    
    // 1. Calc Coords
    let tx = Math.round((x * ratio) / BLOCK_SIZE) * BLOCK_SIZE;
    let tz = Math.round((z * ratio) / BLOCK_SIZE) * BLOCK_SIZE;
    let ty = Math.max(10, Math.min(y, 120)); // Keep within reasonable bounds
    ty = Math.round(ty / BLOCK_SIZE) * BLOCK_SIZE;

    // 2. Search Existing
    const searchRadius = 32 * BLOCK_SIZE;
    // Iterate chunks (Simplified: Just linear scan logic for clone)
    // In a real DB this would be a spatial query. Here we scan map keys? Too slow. 
    // We will scan a box around target.
    for(let sx = tx - searchRadius; sx <= tx + searchRadius; sx += BLOCK_SIZE*2) {
        for(let sz = tz - searchRadius; sz <= tz + searchRadius; sz += BLOCK_SIZE*2) {
             // Quick Vertical Check
             for (let sy = ty - 20; sy <= ty + 20; sy+=BLOCK_SIZE) {
                 const k = getKey(sx, sy, sz, destDim);
                 const b = worldBlocks.get(k);
                 if (b && b.type === 'nether_portal') {
                     return { x: sx, y: sy, z: sz };
                 }
             }
        }
    }

    // 3. Generate New
    console.log(`Generating Portal in ${destDim} at ${tx},${ty},${tz}`);
    
    // Clear Area (Safety)
    for(let ix=-1; ix<=4; ix++) {
        for(let iz=-2; iz<=2; iz++) {
            for(let iy=0; iy<=5; iy++) {
                const px = tx + ix*BLOCK_SIZE; const py = ty + iy*BLOCK_SIZE; const pz = tz + iz*BLOCK_SIZE;
                const k = getKey(px, py, pz, destDim);
                const b = worldBlocks.get(k);
                if (b && b.type !== 'bedrock') {
                     worldBlocks.delete(k);
                     broadcast({ type: 'block_update', x: px, y: py, z: pz, blockType: 'air', dim: destDim });
                }
            }
        }
    }
    // Floor Platform
    for(let ix=-1; ix<=4; ix++) {
        for(let iz=-2; iz<=2; iz++) {
             const px = tx + ix*BLOCK_SIZE; const pz = tz + iz*BLOCK_SIZE;
             addBlock(px, ty - BLOCK_SIZE, pz, 'obsidian', destDim);
             broadcast({ type: 'block_update', x: px, y: ty - BLOCK_SIZE, z: pz, blockType: 'obsidian', dim: destDim });
        }
    }

    // Frame (X-Aligned)
    const frame = [
        [0,0], [1,0], [2,0], [3,0], // Bottom
        [0,4], [1,4], [2,4], [3,4], // Top
        [0,1], [0,2], [0,3],        // Left
        [3,1], [3,2], [3,3]         // Right
    ];
    frame.forEach(p => {
        const px = tx + p[0]*BLOCK_SIZE; const py = ty + p[1]*BLOCK_SIZE;
        addBlock(px, py, tz, 'obsidian', destDim);
        broadcast({ type: 'block_update', x: px, y: py, z: tz, blockType: 'obsidian', dim: destDim });
    });

    // Portal Blocks
    fillNetherPortal(tx + BLOCK_SIZE, ty + BLOCK_SIZE, tz, 1, 0, destDim);

    return { x: tx + BLOCK_SIZE, y: ty + BLOCK_SIZE, z: tz };
}

function checkPortalServer(ox, oy, oz, dim) {
    for(let cx=ox-15; cx<=ox+15; cx+=5) for(let cz=oz-15; cz<=oz+15; cz+=5) {
        let complete=true;
        const frames = [
            {x:-1,z:-2},{x:0,z:-2},{x:1,z:-2},
            {x:-1,z:2},{x:0,z:2},{x:1,z:2},
            {x:-2,z:-1},{x:-2,z:0},{x:-2,z:1},
            {x:2,z:-1},{x:2,z:0},{x:2,z:1}
        ];
        
        for(let f of frames) {
            const k = getKey(cx + f.x*5, oy, cz + f.z*5, dim);
            const blockData = worldBlocks.get(k);
            if(!blockData || blockData.type !== 'end_frame_filled') {
                complete = false;
                break;
            }
        }
        
        if(complete) {
            for(let x=-1; x<=1; x++) for(let z=-1; z<=1; z++) {
                const px = cx+x*5, py = oy, pz = cz+z*5;
                addBlock(px, py, pz, 'portal', dim);
                broadcast({ type: 'block_update', x: px, y: py, z: pz, blockType: 'portal', dim: dim, state: {} });
            }
        }
    }
}

function broadcast(msg) {
    const s = JSON.stringify(msg);
    wss.clients.forEach(c => { if(c.readyState === WebSocket.OPEN) c.send(s); });
}

function getClientById(id) {
    for (const client of wss.clients) {
        if (client.playerId === id) return client;
    }
    return null;
}

function assignHost() {
    if (players.size === 0) {
        hostId = null;
        return;
    }
    if (!hostId || !players.has(hostId)) {
        const nextPlayer = players.keys().next().value;
        hostId = nextPlayer;
        const pData = players.get(hostId);
        pData.mode = 'creative'; 
        pData.health = 20; 
        console.log(`New Host Assigned: ${pData.username} (${hostId})`);
        
        const client = getClientById(hostId);
        if (client) client.send(JSON.stringify({ type: 'gamemode', mode: 'creative', isHost: true }));
    }
}

function getArchetypeForBlock(blockType) {
    if (['wood', 'door'].includes(blockType)) return 'bouncy';
    if (['packed_ice', 'snow_block'].includes(blockType)) return 'sliding';
    if (['leaves', 'crop'].includes(blockType)) return 'floating';
    if (['magma', 'red_mushroom', 'cactus'].includes(blockType)) return 'sticky';
    if (['obsidian', 'stone', 'end_stone', 'netherrack'].includes(blockType)) return 'heavy';
    if (blockType === 'flint_and_steel') return 'explosive';
    return 'default';
}

function getStarterInventory() {
    return {
        'grass': 0, 'dirt': 10, 'stone': 10, 'wood': 10, 
        'leaves': 0, 'sand': 0, 'cactus': 0, 
        'end_frame': 0, 'eye_of_ender': 0, 'end_stone': 0, 
        'emerald': 0,
        'packed_ice': 0, 'snow_block': 0,
        'netherrack': 0, 'glowstone': 0, 'flint_and_steel': 1,
        'blaze_rod': 0, 'nether_brick': 0, 'spawner': 0,
        'quartz_ore': 0, 'magma': 0, 'red_mushroom': 0, 'quartz': 0, 'gold_nugget': 0,
        'sulfur_block': 0, 'cinnabar': 0, 'potent_sulfur': 0, '2fa_block': 0, 'corrupted_2fa_block': 0,
        'sandstone': 0, 'cobblestone': 0, 'market_awning': 0, 'market_carpet_1': 0, 'market_carpet_2': 0, 'market_sign': 0, 'stick_roof': 0,
        'healing_salve': 0, 'void_charm': 0,
        'lead_flask': 0, 'helium_flask': 0, 'midas_flask': 0, 'martyr_flask': 0,
        'frozen_chest': 0,
        'cherry_leaves': 0, 'lily_pad': 0, 'flower_white': 0, 'flower_pink': 0, 'vine': 0, 
        'chain': 0, 'lantern': 0, 'wooden_slab': 0, 'fence': 0, 'red_carpet': 0, 'void_sign': 0,
        'ice_shard': 0, 'ice_knife': 0, 'determination_flask': 0, 'dark_candy': 0, 'dark_dollar': 0,
        'dark_grass': 0, 'dark_tree_log': 0, 'dark_tree_leaves': 0, 'dark_brick': 0, 'deltarune_chest': 0,
        'cyber_floor': 0, 'cyber_wire': 0, 'cyber_building': 0
    };
}

wss.on('connection', ws => {
    const id = Math.random().toString(36).substr(2, 9);
    ws.playerId = id;

    let mode = 'survival';
    if (players.size === 0) {
        mode = 'creative';
        hostId = id;
    }

    // Placeholder initial state. Will be overwritten on join if restoring a session.
    let initialPlayer = { 
        id: id, sessionId: Math.random().toString(36).substr(2, 9),
        x: 0, y: 60, z: 0, dim: 'overworld', username: 'Guest', mode: mode,
        health: 20, maxHealth: 20, inventory: getStarterInventory(), lastDamageTime: 0,
        authenticated: false
    };
    players.set(id, initialPlayer);

    ws.on('message', msg => {
        try {
            const d = JSON.parse(msg);
            let p = players.get(id);
            
            if(d.type === 'join') {
                if (!disableVersionCheck && d.version !== SERVER_VERSION) {
                    ws.send(JSON.stringify({ type: 'kick', message: `Client version mismatch! Server requires v${SERVER_VERSION}. Please update your game.` }));
                    setTimeout(() => ws.close(), 100);
                    return;
                }

                // Check if this is a reconnecting client post-anomaly or normal restart
                let recoveredSessionId = null;
                if (d.sessionId && pendingSessions.has(d.sessionId)) {
                    recoveredSessionId = d.sessionId;
                } else {
                    // Fallback: match by username for normal server restarts
                    for (const [sId, sData] of pendingSessions.entries()) {
                        if (sData.username === d.username) {
                            recoveredSessionId = sId;
                            break;
                        }
                    }
                }

                if (recoveredSessionId) {
                    const savedPlayer = pendingSessions.get(recoveredSessionId);
                    savedPlayer.id = id;
                    savedPlayer.username = d.username;
                    players.set(id, savedPlayer);
                    pendingSessions.delete(recoveredSessionId);
                    p = savedPlayer; // Update reference
                    
                    if (hostSessionId === recoveredSessionId) hostId = id;
                    console.log(`${d.username} reconnected and restored their state.`);
                } else {
                    p.username = d.username;
                    console.log(`${d.username} joined as ${p.mode}`);
                }
                
                ws.send(JSON.stringify({
                    type: 'gamemode',
                    mode: p.mode,
                    isHost: (id === hostId)
                }));
                ws.send(JSON.stringify({ type: 'inventory_update', inventory: p.inventory }));
                ws.send(JSON.stringify({ type: 'status_sync', authenticated: p.authenticated, regenTimer: p.regenTimer || 0, voidWalkerTimer: p.voidWalkerTimer || 0, immovableTimer: p.immovableTimer || 0, heliumTimer: p.heliumTimer || 0, midasTimer: p.midasTimer || 0 }));

                for (const [key, blockData] of worldBlocks) {
                    const keySplit = key.split(',');
                    ws.send(JSON.stringify({ 
                        type: "block_update", 
                        x: parseInt(keySplit[0]), 
                        y: parseInt(keySplit[1]), 
                        z: parseInt(keySplit[2]), 
                        blockType: blockData.type,
                        state: blockData.state,
                        dim: keySplit[3] 
                    }));
                }
                ws.send(JSON.stringify({ type: "world_ready" }));
            }

            if(d.type === 'move') { 
                if(p) { p.x=d.x; p.y=d.y; p.z=d.z; p.yaw=d.yaw; p.dim=d.dim; } 
            }

            if (d.type === 'set_gamemode') {
                if (d.mode !== 'survival') return;
                p.mode = 'survival';
                p.health = Math.max(1, p.health || 20);
                ws.send(JSON.stringify({ type: 'gamemode', mode: 'survival', isHost: (id === hostId) }));
                ws.send(JSON.stringify({ type: 'damage', health: p.health }));
            }

            if (d.type === 'chat') {
                if (!p || !p.username) return;
                const message = (d.message || '').toString().trim().slice(0, 140);
                if (!message) return;
                
                broadcast({ type: 'chat', username: p.username, message });
            }

            if(d.type === 'block_place') {
                if (p.mode === 'survival') {
                    if (p.inventory[d.blockType] && p.inventory[d.blockType] > 0) {
                        p.inventory[d.blockType]--;
                        ws.send(JSON.stringify({ type: 'inventory_update', inventory: p.inventory }));
                    } else {
                        return; 
                    }
                }

                addBlock(d.x, d.y, d.z, d.blockType, d.dim, d.state || {});
                broadcast({ type:'block_update', x:d.x, y:d.y, z:d.z, blockType:d.blockType, dim:d.dim, state: d.state || {} });

                if (d.blockType === 'obsidian') {
                    trySummonDiddyGolemServer(d.x, d.y, d.z, d.dim);
                }
                
                // Register Spawner if placed by player
                if (d.blockType === 'spawner') {
                    const mType = (d.state && d.state.type) ? d.state.type : (p.dim === 'the_nether' ? 'blaze' : (p.x < -600 ? 'frostbound' : 'zombie'));
                    spawners.push({ x: bx, y: by, z: bz, dim: p.dim, timer: 0, mobType: mType });
                }

                if(d.blockType === 'end_frame_filled') checkPortalServer(d.x, d.y, d.z, d.dim);

                // SCHEDULE FLUID UPDATE
                if (d.blockType === 'water' || d.blockType === 'lava') scheduleFluidUpdate(d.x, d.y, d.z, d.dim); 
                wakeNeighbors(d.x, d.y, d.z, d.dim); 
                checkMarketQuestServer(d.dim);
            }
            
            // New handler for updating state only (toggling doors etc)
            if (d.type === 'block_state_update') {
                const k = getKey(d.x, d.y, d.z, d.dim);
                const existing = worldBlocks.get(k);
                if (existing) {
                    const newState = { ...existing.state, ...d.state };
                    console.log(newState);
                    worldBlocks.set(k, { type: existing.type, state: newState });
                    broadcast({ 
                        type: 'block_update', 
                        x: d.x, y: d.y, z: d.z, 
                        blockType: existing.type, 
                        state: newState, 
                        dim: d.dim 
                    });
                }
            }

            if(d.type === 'block_break') {
                const k = getKey(d.x, d.y, d.z, d.dim);
                const existing = worldBlocks.get(k);
                const existingType = existing ? existing.type : null;
                
                if (existingType && existingType !== 'air') {
                    if (p.mode === 'survival' && UNBREAKABLE_BLOCKS.includes(existingType)) {
                        if (!(existingType === '2fa_block' && p.authenticated)) {
                            return;
                        }
                    }

                    if (p.mode === 'survival') {
                        let drop = existingType;
                        if (drop === 'end_frame_filled') drop = 'end_frame'; 
                        if (drop === 'quartz_ore') drop = 'quartz'; // Drop item
                        
                        if (existingType === 'frozen_chest') {
                            const drops = ['emerald', 'emerald', 'healing_salve', 'gold_nugget', 'lead_flask'];
                            drop = drops[Math.floor(Math.random() * drops.length)];
                            if (p.inventory[drop] !== undefined) {
                                p.inventory[drop] += (drop === 'emerald' ? 3 : 1);
                                ws.send(JSON.stringify({ type: 'inventory_update', inventory: p.inventory }));
                            }
                        } else if (existingType === 'deltarune_chest') {
                            const isCandy = Math.random() > 0.5;
                            drop = isCandy ? 'dark_candy' : 'dark_dollar';
                            p.inventory[drop] = (p.inventory[drop] || 0) + (isCandy ? 1 : 5);
                            ws.send(JSON.stringify({ type: 'inventory_update', inventory: p.inventory }));
                        } else if (p.inventory[drop] !== undefined) {
                            p.inventory[drop]++;
                            ws.send(JSON.stringify({ type: 'inventory_update', inventory: p.inventory }));
                        }
                    }

                    // Remove Spawner from logic list if broken
                    if (existingType === 'spawner') {
                        const idx = spawners.findIndex(s => s.x === d.x && s.y === d.y && s.z === d.z && s.dim === d.dim);
                        if (idx > -1) spawners.splice(idx, 1);
                    }

                    worldBlocks.delete(k);
                    broadcast({ type:'block_update', x:d.x, y:d.y, z:d.z, blockType:'air', dim:d.dim });

                    // WAKE FLUIDS
                    wakeNeighbors(d.x, d.y, d.z, d.dim);
                }
            }

            if (d.type === 'entity_hit') {
                // Prevent using weapons if inventory is empty
                if (p.mode === 'survival' && (!p.inventory[d.weapon] || p.inventory[d.weapon] <= 0)) {
                    d.weapon = 'fist';
                }
                const mob = mobs.find(m => m.id === d.mob);
                if (mob) {
                    // --- BATTLE SYSTEM INTERCEPTION ---
                    if (mob.type === 'lancer' || (mob.battle && mob.battle.active)) {
                        if (!mob.battle || !mob.battle.active) {
                            startDeltaruneBattle(mob, p);
                            return; // Stop initial damage, start battle instead
                        }
                        if (!mob.battle.vulnerable) {
                            return; // Ignore damage if not in player real-time phase
                        }
                    }
                    if ((mob.type.startsWith('void') || mob.type === 'owca') && d.weapon === '2fa_block') {
                        if (p.mode === 'survival' && p.inventory['2fa_block'] > 0) {
                            p.inventory['2fa_block']--;
                            p.inventory['corrupted_2fa_block'] = (p.inventory['corrupted_2fa_block'] || 0) + 1;
                            ws.send(JSON.stringify({ type: 'inventory_update', inventory: p.inventory }));
                        }
                        createVoidExplosion(mob.x, mob.y, mob.z, mob.dim);
                        
                        if (mob.type === 'owca') {
                            mob.health = 30;
                            mob.x += 10000;
                        } else {
                            mob.isDead = true;
                        }
                        broadcast({ type:'entity_update', mob });
                        return;
                    } else if (mob.type === 'end_crystal') {
                        mob.isDead = true;
                        broadcast({ type:'entity_update', mob });
                        createExplosion(mob.x, mob.y, mob.z, mob.dim, 6);
                    } else if (mob.type === 'sulfur_cube') {
                        const dmg = d.weapon === 'hammer' ? 5 : (d.weapon === 'ice_knife' ? 3 : 1);
                        mob.vy = 50 * dmg;
                        mob.vx = (d.dirX || 0) * 100 * dmg;
                        mob.vz = (d.dirZ || 0) * 100 * dmg;
                        broadcast({ type:'entity_update', mob });
                    } else {
                        const dmg = d.weapon === 'hammer' ? 5 : (d.weapon === 'ice_knife' ? 3 : 1);
                        mob.health -= dmg;
                        
                        if (d.weapon === 'hammer') {
                            mob.vy = 500;
                            mob.vx = (d.dirX || 0) * 1000;
                            mob.vz = (d.dirZ || 0) * 1000;
                        }
                        
                        // Pigman Aggro (Immediate on Hit)
                        if (mob.type === 'pigman') {
                            mob.aiState.mode = 'aggressive';
                            mob.aiState.targetId = p.id; // Target the attacker
                        }

                        if (mob.health <= 0) {
                            mob.isDead = true;
                            // Drops
                            if (p.mode === 'survival') {
                                if (mob.type === 'blaze') p.inventory['blaze_rod'] = (p.inventory['blaze_rod'] || 0) + 1;
                                if (mob.type === 'pigman') p.inventory['gold_nugget'] = (p.inventory['gold_nugget'] || 0) + 1;
                                if (mob.type === 'diddy') p.inventory['eye_of_ender'] = (p.inventory['eye_of_ender'] || 0) + 1;
                                ws.send(JSON.stringify({ type: 'inventory_update', inventory: p.inventory }));
                            }
                            if (mob.battle && mob.battle.active) endDeltaruneBattle(mob);
                        }
                        broadcast({ type:'entity_update', mob });
                    }
                } else {
                    const targetPlayer = players.get(d.mob);
                    if (targetPlayer && targetPlayer.mode === 'survival') {
                        const dmg = d.weapon === 'hammer' ? 5 : (d.weapon === 'ice_knife' ? 3 : 1);
                        targetPlayer.health -= dmg;
                        
                        const victimClient = getClientById(targetPlayer.id);
                        if (victimClient) {
                            victimClient.send(JSON.stringify({ type: 'damage', health: targetPlayer.health }));
                            if (d.weapon === 'hammer') {
                                victimClient.send(JSON.stringify({
                                    type: 'knockback',
                                    vx: (d.dirX || 0) * 1000,
                                    vy: 500,
                                    vz: (d.dirZ || 0) * 1000
                                }));
                            }
                        }
                        
                        if (targetPlayer.health <= 0) {
                            if (targetPlayer.in2FAFlow) fail2FAServer(targetPlayer);
                            else {
                                targetPlayer.health = 20;
                                targetPlayer.x = 0; targetPlayer.y = 60; targetPlayer.z = 0; 
                                if (victimClient) victimClient.send(JSON.stringify({ type: 'respawn', x:0, y:60, z:0 }));
                            }
                        }
                    }
                }
            }

            // --- PLAYER INTERACTS WITH ENTITY ---
            if (d.type === 'void_save') {
                p.voidWalkerTimer = 0;
                ws.send(JSON.stringify({ type: 'status_sync', regenTimer: p.regenTimer, voidWalkerTimer: 0, immovableTimer: p.immovableTimer, heliumTimer: p.heliumTimer, midasTimer: p.midasTimer, determinationTimer: p.determinationTimer, woolChestProgress: p.woolChestProgress }));
            }

            if (d.type === 'consume_item') {
                if (p.mode === 'survival') {
                    if (!p.inventory[d.item] || p.inventory[d.item] <= 0) return;
                    p.inventory[d.item]--;
                    ws.send(JSON.stringify({ type: 'inventory_update', inventory: p.inventory }));
                }
                if (d.item === 'healing_salve') {
                    p.regenTimer = 30.0; p.regenTick = 0;
                } else if (d.item === 'void_charm') {
                    p.voidWalkerTimer = 120.0;
                } else if (d.item === 'lead_flask') {
                    p.immovableTimer = 30.0;
                } else if (d.item === 'helium_flask') {
                    p.heliumTimer = 30.0;
                } else if (d.item === 'midas_flask') {
                    p.midasTimer = 30.0;
                } else if (d.item === 'martyr_flask') {
                    createVoidExplosion(p.x, p.y, p.z, p.dim);
                } else if (d.item === 'determination_flask') {
                    p.determinationTimer = 30.0;
                } else if (d.item === 'dark_candy') {
                    p.health = Math.min(20, p.health + 5);
                    const client = getClientById(p.id);
                    if (client) client.send(JSON.stringify({ type: 'damage', health: p.health }));
                }
                ws.send(JSON.stringify({ type: 'status_sync', regenTimer: p.regenTimer, voidWalkerTimer: p.voidWalkerTimer, immovableTimer: p.immovableTimer, heliumTimer: p.heliumTimer, midasTimer: p.midasTimer, determinationTimer: p.determinationTimer }));
            }

            if (d.type === 'interact_wool_chest') {
                if (p.hasOwca) {
                    ws.send(JSON.stringify({ type: 'chat', username: 'SYSTEM', message: 'You have already unlocked an owca.' }));
                    return;
                }
                if (!p.woolChestProgress) p.woolChestProgress = { charm: false, shards: 0 };
                
                if (d.heldItem === 'void_charm' && (p.mode === 'creative' || p.inventory['void_charm'] > 0) && !p.woolChestProgress.charm) {
                    if (p.mode === 'survival') p.inventory['void_charm']--; 
                    p.woolChestProgress.charm = true;
                    ws.send(JSON.stringify({ type: 'inventory_update', inventory: p.inventory }));
                } else if (d.heldItem === 'ice_shard' && (p.mode === 'creative' || p.inventory['ice_shard'] > 0) && p.woolChestProgress.shards < 10) {
                    if (p.mode === 'survival') p.inventory['ice_shard']--; 
                    p.woolChestProgress.shards++;
                    ws.send(JSON.stringify({ type: 'inventory_update', inventory: p.inventory }));
                }
                ws.send(JSON.stringify({ type: 'status_sync', woolChestProgress: p.woolChestProgress }));
                
                if (p.woolChestProgress.charm && p.woolChestProgress.shards >= 10) {
                    p.hasOwca = true;
                    const mob = spawnMob('owca', d.x, d.y + 10, d.z, d.dim);
                    mob.ownerId = p.id;
                    ws.send(JSON.stringify({ type: 'chat', username: 'SYSTEM', message: 'The Wool Chest opens... an owca appears.' }));
                    broadcast({ type: 'spawner_particles', x: d.x, y: d.y, z: d.z, dim: d.dim });
                }
                return;
            }

            if (d.type === 'entity_interact') {
                const targetMob = mobs.find(m => m.id === d.targetId);
                
                if (targetMob && !targetMob.isDead && targetMob.dim === p.dim) {
                    const dist = Math.hypot(p.x - targetMob.x, p.y - targetMob.y, p.z - targetMob.z);
                    if (dist < 5 * BLOCK_SIZE) {
                        if (targetMob.type === 'scc') {
                            const client = getClientById(p.id);
                            if (client) client.send(JSON.stringify({ type: 'open_scc_shop' }));
                            return;
                        } else if (targetMob.type === 'ralsei' && !targetMob.inParty) {
                            targetMob.inParty = true;
                            targetMob.ownerId = p.id;
                            broadcast({ type: 'entity_update', mob: targetMob });
                            ws.send(JSON.stringify({ type: 'deltarune_text', text: [
                                "* Welcome, Heroes of Light...",
                                "* I am Ralsei, the Prince of this Kingdom...",
                                "* The balance of Light and Dark is crumbling...",
                                "* Please, let me join your party to save the world!",
                                "* (Ralsei joined the party!)",
                                "* (The Great Door slowly grinds open...)"
                            ]}));
                            
                            // Open the Great Door
                            const updates = [];
                            for (const [k, blockData] of worldBlocks) {
                                if (blockData.state && blockData.state.isGreatDoor) {
                                    const parts = k.split(',');
                                    worldBlocks.delete(k);
                                    updates.push({ x: parseInt(parts[0]), y: parseInt(parts[1]), z: parseInt(parts[2]), type: 'air', dim: parts[3] });
                                }
                            }
                            if (updates.length > 0) broadcast({ type: 'world_sync', modifications: updates });
                        } else if (p.mode === 'survival' && (targetMob.type === 'villager' || targetMob.type === 'merchant' || targetMob.type === 'mercator' || targetMob.type === 'tork')) {
                            targetMob.tradingWith = id; 
                            if (p.authenticated && targetMob.type === 'villager') {
                                if (!targetMob.trades.some(t => t.rewardItem === '2fa_block')) {
                                    targetMob.trades.push({ costItem: 'emerald', costCount: 10, rewardItem: '2fa_block', rewardCount: 1 });
                                }
                            }
                            ws.send(JSON.stringify({ 
                                type: 'open_trade', 
                                trades: targetMob.trades, 
                                traderId: targetMob.id 
                            }));
                        } else if (targetMob.type === 'sulfur_cube') {
                            const heldItem = d.heldItem;
                            if (p.mode === 'creative' || (p.inventory[heldItem] && p.inventory[heldItem] > 0)) {
                                if (p.mode === 'survival') {
                                    p.inventory[heldItem]--;
                                    ws.send(JSON.stringify({ type: 'inventory_update', inventory: p.inventory }));
                                }
                                
                                targetMob.archetype = getArchetypeForBlock(heldItem);
                                targetMob.eatenBlock = heldItem;
                                targetMob.explodeTimer = 0;
                                targetMob.vy = 50; // Pop up into the air when fed!
                                broadcast({ type: 'entity_update', mob: targetMob });
                            }
                        }
                    }
                }
            }

            // --- NEW: TRADE CLOSED ---
            if (d.type === 'trade_closed') {
                // Find any mob trading with this player and free them
                const mob = mobs.find(m => m.tradingWith === id);
                if (mob) {
                    mob.tradingWith = null;
                }
            }

            if (d.type === 'scc_transaction') {
                if (p.mode !== 'survival') return;
                const costItem = d.action === 'buy' ? 'dark_dollar' : d.item;
                const rewardItem = d.action === 'buy' ? d.item : 'dark_dollar';
                
                if ((p.inventory[costItem] || 0) >= d.cost) {
                    p.inventory[costItem] -= d.cost;
                    p.inventory[rewardItem] = (p.inventory[rewardItem] || 0) + d.reward;
                    ws.send(JSON.stringify({ type: 'inventory_update', inventory: p.inventory }));
                    ws.send(JSON.stringify({ type: 'trade_success' }));
                } else {
                    ws.send(JSON.stringify({ type: 'trade_fail' }));
                }
            }

            // --- PLAYER EXECUTES TRADE ---
            if (d.type === 'trade_execute') {
                if (p.mode !== 'survival') return;

                // Find the specific villager we are trading with
                const targetMob = mobs.find(m => m.id === d.traderId);
                
                // Security: Ensure mob exists, is close, and has the trade index
                if (!targetMob || targetMob.isDead || !targetMob.trades[d.tradeIndex]) {
                    ws.send(JSON.stringify({ type: 'trade_fail' }));
                    return;
                }
                
                // Distance check (prevent trading across map if menu stays open)
                const dist = Math.hypot(p.x - targetMob.x, p.y - targetMob.y, p.z - targetMob.z);
                if (dist > 6 * BLOCK_SIZE) { // Match interaction reach + buffer
                    ws.send(JSON.stringify({ type: 'trade_fail' }));
                    return;
                }

                const trade = targetMob.trades[d.tradeIndex];
                
                // Validate inventory
                let canAfford = (p.inventory[trade.costItem] || 0) >= trade.costCount;
                if (trade.costItem2 && (p.inventory[trade.costItem2] || 0) < trade.costCount2) canAfford = false;
                if (canAfford) {
                    // Execute Trade
                    p.inventory[trade.costItem] -= trade.costCount;
                    if (trade.costItem2) p.inventory[trade.costItem2] -= trade.costCount2;
                    p.inventory[trade.rewardItem] = (p.inventory[trade.rewardItem] || 0) + trade.rewardCount;
                    
                    ws.send(JSON.stringify({ type: 'inventory_update', inventory: p.inventory }));
                    ws.send(JSON.stringify({ type: 'trade_success' }));
                } else {
                    ws.send(JSON.stringify({ type: 'trade_fail' }));
                }
            }

            // --- HOST TOGGLES GAMEMODE ---
            if (d.type === 'spawn_egg') {
                if (p.mode === 'creative') {
                    spawnMob(d.mobType, d.x, d.y, d.z, d.dim || p.dim);
                }
            }

            if (d.type === 'submit_totp') {
                if (p.in2FAFlow && p.totpSecret) {
                    if (verifyTOTP(p.totpSecret, d.code)) {
                        p.in2FAFlow = false;
                        p.totpSecret = null;
                        p.authenticated = true;
                        p.dim = p.pre2FAPos.dim;
                        p.x = p.pre2FAPos.x; p.y = p.pre2FAPos.y; p.z = p.pre2FAPos.z;
                        const client = getClientById(p.id);
                        if (client) {
                            client.send(JSON.stringify({ type: 'teleport', x: p.x, y: p.y, z: p.z, dim: p.dim }));
                            client.send(JSON.stringify({ type: 'chat', username: 'SYSTEM', message: '2FA COMPLETE: Access granted.' }));
                            client.send(JSON.stringify({ type: 'close_totp' }));
                            client.send(JSON.stringify({ type: '2fa_success' }));
                        }
                    } else {
                        const client = getClientById(p.id);
                        if (client) client.send(JSON.stringify({ type: 'chat', username: 'SYSTEM', message: 'Invalid TOTP code.' }));
                    }
                }
            }

            // --- BATTLE ACTIONS ---
            if (d.type === 'battle_action') {
                const mob = mobs.find(m => m.id === d.mobId);
                if (!mob || !mob.battle || !mob.battle.active) return;
                
                const client = getClientById(p.id);

                if (d.action === 'fight') {
                    // Real-time Minecraft attack phase
                    mob.battle.state = 'player_action_realtime';
                    mob.battle.vulnerable = true;
                    mob.battle.timer = 5.0; // 5 Seconds to attack
                    if (client) client.send(JSON.stringify({ type: 'battle_state', state: 'player_action_realtime' }));
                } else if (d.action === 'party_fight') {
                    // Turn-based party attack
                    mob.health -= d.damage;
                    broadcast({ type: 'entity_update', mob: mob });
                    
                    if (mob.health <= 0) {
                        endDeltaruneBattle(mob);
                    } else {
                        // Immediately go to enemy turn
                        mob.battle.state = 'enemy_turn_realtime';
                        mob.battle.vulnerable = false;
                        mob.battle.timer = 7.0;
                        if (client) client.send(JSON.stringify({ type: 'battle_state', state: 'enemy_turn_realtime' }));
                    }
                } else if (d.action === 'act') {
                    // Specific to Lancer for tutorial
                    mob.battle.tired = true;
                    if (client) client.send(JSON.stringify({ type: 'chat', username: 'SYSTEM', message: '* You told Lancer his bike looks cool. He seems tired.' }));
                    mob.battle.state = 'enemy_turn_realtime';
                    mob.battle.timer = 7.0;
                    if (client) client.send(JSON.stringify({ type: 'battle_state', state: 'enemy_turn_realtime' }));
                } else if (d.action === 'magic') {
                    if (mob.battle.tired) {
                        if (client) client.send(JSON.stringify({ type: 'chat', username: 'SYSTEM', message: '* Ralsei used Pacify!' }));
                        endDeltaruneBattle(mob);
                    } else {
                        if (client) client.send(JSON.stringify({ type: 'chat', username: 'SYSTEM', message: '* Ralsei tried to Pacify, but the enemy is not tired.' }));
                        mob.battle.state = 'enemy_turn_realtime';
                        mob.battle.timer = 7.0;
                        if (client) client.send(JSON.stringify({ type: 'battle_state', state: 'enemy_turn_realtime' }));
                    }
                } else if (d.action === 'spare') {
                    if (mob.battle.tired) {
                        if (client) client.send(JSON.stringify({ type: 'chat', username: 'SYSTEM', message: '* You spared the enemy!' }));
                        endDeltaruneBattle(mob);
                    } else {
                        if (client) client.send(JSON.stringify({ type: 'chat', username: 'SYSTEM', message: '* The enemy is not ready to be spared.' }));
                        mob.battle.state = 'enemy_turn_realtime';
                        mob.battle.timer = 7.0;
                        if (client) client.send(JSON.stringify({ type: 'battle_state', state: 'enemy_turn_realtime' }));
                    }
                }
            }

            if (d.type === 'ch3_win') {
                const hasOwca = mobs.find(m => m.type === 'owca' && m.ownerId === p.id);
                if (hasOwca) {
                    ws.send(JSON.stringify({ type: 'deltarune_text', text: [
                        "* You survived the TV Show.",
                        "* Owca continued and played deltarune without you.",
                        "* The titan was defeated.",
                        "* (You got 100 Emeralds!)"
                    ]}));
                    p.inventory['emerald'] = (p.inventory['emerald'] || 0) + 100;
                    ws.send(JSON.stringify({ type: 'inventory_update', inventory: p.inventory }));
                    setTimeout(() => {
                        p.x = 0; p.y = 60; p.z = 0; p.dim = 'overworld';
                        ws.send(JSON.stringify({ type: 'teleport', x: 0, y: 60, z: 0, dim: 'overworld' }));
                        const pRalsei = mobs.find(m => m.type === 'ralsei' && m.ownerId === p.id);
                        if (pRalsei) { pRalsei.dim = 'overworld'; pRalsei.x = 5; pRalsei.y = 60; pRalsei.z = 0; broadcast({ type: 'entity_update', mob: pRalsei }); }
                        const pOwca = mobs.find(m => m.type === 'owca' && m.ownerId === p.id);
                        if (pOwca) { pOwca.dim = 'overworld'; pOwca.x = -5; pOwca.y = 60; pOwca.z = 0; broadcast({ type: 'entity_update', mob: pOwca }); }
                        
                        for (const k of worldBlocks.keys()) { if (k.endsWith(',dark_world')) worldBlocks.delete(k); }
                        for (let i = mobs.length - 1; i >= 0; i--) { if (mobs[i].dim === 'dark_world' && !mobs[i].inParty) mobs[i].isDead = true; }
                        broadcast({ type: 'reset_dimension', dim: 'dark_world' });
                        generateDarkWorldServer(); 
                    }, 8000);
                } else {
                    ws.send(JSON.stringify({ type: 'deltarune_text', text: [
                        "* You survived the TV Show.",
                        "* But the earth shakes...",
                        "* Falling into the abyss of Chapter 4..."
                    ]}));
                    setTimeout(() => {
                        for (const k of worldBlocks.keys()) { if (k.endsWith(',dark_world')) worldBlocks.delete(k); }
                        for (let i = mobs.length - 1; i >= 0; i--) { if (mobs[i].dim === 'dark_world' && !mobs[i].inParty) mobs[i].isDead = true; }
                        broadcast({ type: 'reset_dimension', dim: 'dark_world' });
                        
                        const updates = [];
                        for(let x=-20; x<=20; x++) { 
                            for(let z=-20; z<=20; z++) { 
                                addBlock(x*5, 0, z*5, 'bedrock', 'dark_world'); 
                                updates.push({ x: x*5, y: 0, z: z*5, type: 'bedrock', dim: 'dark_world' });
                            } 
                        }
                        if (updates.length > 0) broadcast({ type: 'world_sync', modifications: updates });

                        const t = spawnMob('titan', 0, 10, 40, 'dark_world'); t.titanEncounter = true;
                        spawnMob('knight', 0, 5, 20, 'dark_world');
                        
                        p.x = 0; p.y = 20; p.z = 0; p.dim = 'dark_world';
                        ws.send(JSON.stringify({ type: 'teleport', x: 0, y: 20, z: 0, dim: 'dark_world' }));
                        
                        const pRalsei = mobs.find(m => m.type === 'ralsei' && m.ownerId === p.id);
                        if (pRalsei) { pRalsei.x = 5; pRalsei.y = 20; pRalsei.z = 0; broadcast({ type: 'entity_update', mob: pRalsei }); }
                    }, 8000);
                }
            }

            if (d.type === 'admin_gamemode_toggle') {
                if (d.targetId === 'self') d.targetId = id;
                // Security Check: Only the Host can do this
                if (id !== hostId) return;

                const targetPlayer = players.get(d.targetId);
                if (targetPlayer) {
                    // Toggle Mode
                    targetPlayer.mode = (targetPlayer.mode === 'creative') ? 'survival' : 'creative';
                    
                    // Reset health if switching to survival
                    if (targetPlayer.mode === 'survival') targetPlayer.health = 20;

                    // Notify Target
                    const targetClient = getClientById(d.targetId);
                    if (targetClient) {
                        targetClient.send(JSON.stringify({ type: 'gamemode', mode: targetPlayer.mode, isHost: (d.targetId === hostId) }));
                        // If switching to survival, ensure they have health UI update
                        targetClient.send(JSON.stringify({ type: 'damage', health: targetPlayer.health }));
                    }

                    // Notify Everyone (to update nametags/behavior if needed)
                    console.log(`Host toggled ${targetPlayer.username} to ${targetPlayer.mode}`);
                }
            }
            // --- ACTIVATE END FRAME ---
            if (d.type === 'activate_end_frame') {
                // 1. Check Dist
                const dist = Math.hypot(p.x - d.x, p.y - d.y, p.z - d.z);
                if (dist > 10 * BLOCK_SIZE) return;

                // 2. Check Block is Frame
                const key = getKey(d.x, d.y, d.z, d.dim);
                const block = worldBlocks.get(key);
                if (!block || block.type !== 'end_frame') return;

                // 3. Check/Consume Item
                if (p.mode === 'survival') {
                    if (!p.inventory['eye_of_ender'] || p.inventory['eye_of_ender'] <= 0) return;
                    p.inventory['eye_of_ender']--;
                    ws.send(JSON.stringify({ type: 'inventory_update', inventory: p.inventory }));
                }

                // 4. Update Block
                worldBlocks.set(key, { type: 'end_frame_filled', state: {} });
                broadcast({ type: 'block_update', x: d.x, y: d.y, z: d.z, blockType: 'end_frame_filled', dim: d.dim, state: {} });
                
                // 5. Check Portal
                checkPortalServer(d.x, d.y, d.z, d.dim);
            }

            // --- IGNITE NETHER PORTAL ---
            if (d.type === 'ignite_portal') {
                const dist = Math.hypot(p.x - d.x, p.y - d.y, p.z - d.z);
                if (dist > 10 * BLOCK_SIZE) return;
                checkNetherPortalServer(d.x, d.y, d.z, d.dim);
            }

            // --- PLAYER PORTAL TRAVEL ---
            if (d.type === 'create_dark_fountain') {
                p.determinationTimer = 0;
                ws.send(JSON.stringify({ type: 'status_sync', determinationTimer: 0 }));
                
                setTimeout(() => {
                    p.dim = 'dark_world';
                    p.x = 0; p.y = 20; p.z = 0;
                    p.vx = 0; p.vy = 0; p.vz = 0;
                    
                    const owca = mobs.find(m => m.type === 'owca' && m.ownerId === p.id);
                    if (owca) {
                        owca.dim = 'dark_world';
                        owca.x = 5; owca.y = 20; owca.z = 0;
                        broadcast({ type: 'entity_update', mob: owca });
                        ws.send(JSON.stringify({ type: 'deltarune_text', text: [
                            "* Owca fell into the dark world with you.",
                            "* It joined the party!"
                        ]}));
                    }
                    
                    ws.send(JSON.stringify({ 
                        type: 'teleport', 
                        x: p.x, y: p.y, z: p.z, 
                        dim: 'dark_world' 
                    }));
                }, 5500); // Wait for the 5.5s Cutscene to end
            }

            if (d.type === 'portal_travel') {
                let dest = { x: 0, y: 60, z: 0 };
                
                if (d.portalType === 'portal') {
                    // End Portal (Fixed Spawn)
                    dest = { x: 0, y: 60, z: 0 };
                } else {
                    // Nether Portal (Calculated & Generated)
                    dest = findOrGeneratePortal(p.x, p.y, p.z, d.destDim);
                }

                // Update Player
                p.dim = d.destDim;
                p.x = dest.x; p.y = dest.y; p.z = dest.z;
                p.vx = 0; p.vy = 0; p.vz = 0;
                
                // Tell Client to Switch
                ws.send(JSON.stringify({ 
                    type: 'teleport', 
                    x: dest.x, y: dest.y, z: dest.z, 
                    dim: d.destDim 
                }));
            }

            // --- MULTIPLAYER ANOMALIES ---
            if (d.type === 'host_snapshot') {
                hostHTMLSnapshot = d.html;
                console.log("Received pristine reality snapshot from Host.");
            }

            if (d.type === 'trigger_anomaly') {
                if (!hostHTMLSnapshot) {
                    console.error("Cannot trigger anomaly: No host snapshot available.");
                    return;
                }
                console.log("Anomaly triggered in MP! Contacting higher dimensions...");
                
                // Process the OpenAI request asynchronously so the server event loop doesn't block entirely
                (async () => {
                    try {
                        const serverSource = fs.readFileSync(__filename, 'utf8');
                        
                        const promptStr = `You are an anomalous AI entity altering a Javascript voxel game.
The game has a Client (HTML) and a Server (Node.js). I will provide both source codes.
Your task: Add 2 or 3 simple, obvious, and eerie SCP-like anomalies simultaneously.
You MUST include an equal balance of changes that affect GAMEPLAY (Server physics/mechanics) and AMBIENCE (Client visuals/audio).
DO NOT add new mobs or complex AI loops.

Output ONLY diff blocks. Format:
<<<<<<< SEARCH
[exact original code]
=======
[new anomalous code]
>>>>>>> REPLACE

You can target both the Client and Server code in your diffs. Make sure the SEARCH block matches exactly. Keep code robust.`;
                        
                        const userContent = `=== CLIENT HTML ===\n${hostHTMLSnapshot}\n\n=== SERVER JS ===\n${serverSource}`;
                        
                        // Native fetch (requires Node v18+)
                        const response = await fetch('https://api.openai.com/v1/chat/completions', {
                            method: 'POST',
                            headers: { 'Content-Type': 'application/json', 'Authorization': `Bearer ${d.apiKey}` },
                            body: JSON.stringify({
                                model: 'gpt-5-mini',
                                messages: [
                                    { role: 'system', content: promptStr },
                                    { role: 'user', content: userContent }
                                ],
                                max_completion_tokens: 32000
                            })
                        });
                        
                        const data = await response.json();
                        if (data.error) throw new Error(data.error.message);
                        
                        const patch = data.choices[0].message.content;
                        
                        // Patch Applicator Function
                        const applyPatches = (src, ptch) => {
                            let newSrc = src;
                            let searchIdx = ptch.indexOf('<<<<<<< SEARCH');
                            let count = 0;
                            while(searchIdx >= 0) {
                                const pp = ptch.indexOf('=======', searchIdx);
                                const rp = ptch.indexOf('>>>>>>> REPLACE', searchIdx);
                                if(pp < 0 || rp < 0) break;
                                
                                let findStr = ptch.substring(searchIdx + 14, pp).trim();
                                let replaceStr = ptch.substring(pp + 7, rp).replace(/^\n|\n$/g, '');
                                
                                let escapedFind = findStr.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
                                let lenientRegexStr = escapedFind.replace(/\s+/g, '\\s+');
                                
                                try {
                                    const rx = new RegExp(lenientRegexStr, 'g');
                                    if(rx.test(newSrc)) { 
                                        newSrc = newSrc.replace(rx, () => replaceStr); 
                                        count++; 
                                    }
        } catch(e) {}
                                searchIdx = ptch.indexOf('<<<<<<< SEARCH', rp);
                            }
                            return { patched: newSrc, count: count };
                        };
                        
                        const clientRes = applyPatches(hostHTMLSnapshot, patch);
                        const serverRes = applyPatches(serverSource, patch);
                        console.log(`Anomaly shifts applied: Client(${clientRes.count}), Server(${serverRes.count})`);
                        
                        // Save State for Migration
                        saveWorld(clientRes.patched, 'anomaly_server_state.json');
                        
                        // Broadcast to all clients to reboot
                        wss.clients.forEach(c => {
                            if (c.readyState === WebSocket.OPEN) {
                                const pData = players.get(c.playerId);
                                if (pData) {
                                    c.send(JSON.stringify({
                                        type: 'reality_rewritten',
                                        newHTML: clientRes.patched,
                                        sessionId: pData.sessionId
                                    }));
                                }
                            }
                        });
                        
                        // Write temporary server script and spawn detached process
                        fs.writeFileSync('temp_server.js', serverRes.patched);
                        console.log("Rebooting server into anomalous reality... (Check server.log for output)");
                        
                        // Decouple stdio for Windows compatibility and route output to a log file
                        const out = fs.openSync('./server.log', 'a');
                        const err = fs.openSync('./server.log', 'a');
                        
                        const child = spawn(process.argv[0], ['temp_server.js'], { 
                            detached: true, 
                            stdio: ['ignore', out, err] 
                        });
                        
                        child.unref();
                        process.exit();
                        
                    } catch(e) {
                        console.error("MP Anomaly failed:", e);
                    }
                })();
            }

        } catch(e) { console.error("Error handling message:", e); }
    });
    
    ws.on('close', () => {
        // Free any villagers trading with this player
        const mob = mobs.find(m => m.tradingWith === id);
        if (mob) mob.tradingWith = null;

        players.delete(id);
        if (id === hostId) {
            console.log("Host left. Migrating...");
            assignHost();
        }
    });
});

initWorld();

// Auto-save every 60 seconds
setInterval(() => {
    saveWorld();
}, 60000);

// Save on shutdown
function handleShutdown() {
    console.log("\nShutting down server...");
    saveWorld();
    process.exit();
}
process.on('SIGINT', handleShutdown);
process.on('SIGTERM', handleShutdown);

setInterval(() => {
    const time = performance.now();
    const delta = (time - prevTime) / 1000;
    
    ticksThisSecond++;
    if (time - lastTpsTime >= 1000) {
        currentTPS = ticksThisSecond / ((time - lastTpsTime) / 1000);
        ticksThisSecond = 0;
        lastTpsTime = time;
    }

    if (delta > 1.0) { prevTime = time; return; } 
    
    const tickStart = performance.now();
    
    updateMobs(delta);

    // Run fluid sim every tick (or throttle if needed)
    updateFluids(delta);
    
    // Attempt Cave Spawning
    attemptCaveMobSpawning();
    attemptSulfurCubeSpawning();
    attemptVoidlingSpawning();
    attemptMercatorSpawning();
    attemptLynxSpawning();

    // Update Spawners
    updateSpawners(delta);

    // Status Effects & Void Walker physics
    players.forEach(p => {
        if (p.regenTimer > 0) {
            p.regenTimer -= delta;
            p.regenTick = (p.regenTick || 0) + delta;
            if (p.regenTick > 3) {
                p.regenTick = 0;
                if (p.health < 20 && p.health > 0) {
                    p.health++;
                    const client = getClientById(p.id);
                    if (client) client.send(JSON.stringify({ type: 'damage', health: p.health }));
                }
            }
        }
        if (p.voidWalkerTimer > 0) {
            p.voidWalkerTimer -= delta;
            if (p.voidWalkerTimer < 0) p.voidWalkerTimer = 0;
        }
        if (p.immovableTimer > 0) {
            p.immovableTimer -= delta;
            if (p.immovableTimer < 0) p.immovableTimer = 0;
        }
        if (p.heliumTimer > 0) {
            p.heliumTimer -= delta;
            if (p.heliumTimer < 0) p.heliumTimer = 0;
        }
        if (p.midasTimer > 0) {
            p.midasTimer -= delta;
            const bx = Math.round(p.x / BLOCK_SIZE) * BLOCK_SIZE;
            const bz = Math.round(p.z / BLOCK_SIZE) * BLOCK_SIZE;
            const floorY = Math.round((p.y - 12.5) / BLOCK_SIZE) * BLOCK_SIZE;
            const floorK = getKey(bx, floorY, bz, p.dim);
            const floorBlock = worldBlocks.get(floorK);
            
            if (floorBlock && floorBlock.type !== 'air' && floorBlock.type !== 'bedrock') {
                worldBlocks.delete(floorK);
                broadcast({ type: 'block_update', x: bx, y: floorY, z: bz, blockType: 'air', dim: p.dim });
                
                if (p.mode === 'survival') {
                    p.inventory['gold_nugget'] = (p.inventory['gold_nugget'] || 0) + 1;
                    const client = getClientById(p.id);
                    if (client) client.send(JSON.stringify({ type: 'inventory_update', inventory: p.inventory }));
                }
            }
            if (p.midasTimer < 0) p.midasTimer = 0;
        }
        if (p.determinationTimer > 0) {
            p.determinationTimer -= delta;
            p.detTick = (p.detTick || 0) + delta;
            if (p.detTick > 2) {
                p.detTick = 0;
                p.health--;
                const client = getClientById(p.id);
                if (client) client.send(JSON.stringify({ type: 'damage', health: p.health }));
                if (p.health <= 0) {
                    if (p.in2FAFlow) fail2FAServer(p);
                    else {
                        p.health = 20; p.x = 0; p.y = 60; p.z = 0;
                        if (client) client.send(JSON.stringify({ type: 'respawn', x: 0, y: 60, z: 0 }));
                    }
                }
            }
            if (p.determinationTimer < 0) p.determinationTimer = 0;
        }
        
        // Magic Carpet & Sky Lift Check
        const floorK = getKey(Math.round(p.x/5)*5, Math.round((p.y-12.5)/5)*5, Math.round(p.z/5)*5, p.dim);
        const floorBlock = worldBlocks.get(floorK);
        const feetK = getKey(Math.round(p.x/5)*5, Math.round(p.y/5)*5, Math.round(p.z/5)*5, p.dim);
        const feetBlock = worldBlocks.get(feetK);
        const isMagic = (b) => b && b.type === 'market_carpet_2' && b.state && b.state.isMagicCarpet;
        const isSkyLift = (b) => b && b.type === 'lily_pad' && b.state && b.state.isSkyLift;
        
        if (isMagic(floorBlock) || isMagic(feetBlock)) {
            if (!p.carpetCooldown) p.carpetCooldown = 0;
            if (worldTime - p.carpetCooldown > 5.0 || worldTime < p.carpetCooldown) { // 5s cooldown
                p.carpetCooldown = worldTime;
                if (p.x > 10000) { p.x = 315; p.y = 30; p.z = 0; }
                else { p.x = 50015; p.y = 30; p.z = 50000; }
                p.vy = 100;
                const client = getClientById(p.id);
                if (client) {
                    client.send(JSON.stringify({ type: 'teleport', x: p.x, y: p.y, z: p.z, dim: p.dim }));
                    client.send(JSON.stringify({ type: 'chat', username: 'SYSTEM', message: 'The Magic Carpet whisks you away...' }));
                }
            }
        }
        if (isSkyLift(floorBlock) || isSkyLift(feetBlock)) {
            if (!p.carpetCooldown) p.carpetCooldown = 0;
            if (worldTime - p.carpetCooldown > 5.0 || worldTime < p.carpetCooldown) { // 5s cooldown
                p.carpetCooldown = worldTime;
                if (p.y < 100 * BLOCK_SIZE) {
                    p.x = 20015; p.y = 122 * BLOCK_SIZE; p.z = 20000;
                    p.vy = 150;
                    const client = getClientById(p.id);
                    if (client) {
                        client.send(JSON.stringify({ type: 'teleport', x: p.x, y: p.y, z: p.z, dim: p.dim }));
                        client.send(JSON.stringify({ type: 'chat', username: 'SYSTEM', message: 'A geyser of steam blasts you into the Sky Islands!' }));
                    }
                } else {
                    p.x = 15; p.y = 100; p.z = 0;
                    p.vy = 50;
                    const client = getClientById(p.id);
                    if (client) {
                        client.send(JSON.stringify({ type: 'teleport', x: p.x, y: p.y, z: p.z, dim: p.dim }));
                        client.send(JSON.stringify({ type: 'chat', username: 'SYSTEM', message: 'You drop back down to the Overworld.' }));
                    }
                }
            }
        }

        if (p.y < -600) {
            if (p.voidWalkerTimer > 0) {
                p.y = 150;
                p.vy = 800; // Launch out of void
                p.voidWalkerTimer = 0;
                const client = getClientById(p.id);
                if (client) {
                    client.send(JSON.stringify({ type: 'teleport', x: p.x, y: p.y, z: p.z, dim: p.dim }));
                    client.send(JSON.stringify({ type: 'status_sync', regenTimer: p.regenTimer, voidWalkerTimer: 0 }));
                    client.send(JSON.stringify({ type: 'chat', username: 'SYSTEM', message: 'The Void Charm shatters, saving your life!' }));
                }
            }
        }
    });

    // Check Server 2FA Progress
    players.forEach(p => {
        if (p.in2FAFlow) {
            if (!p.totpSecret) {
                const alive = p.authZombies.filter(zid => {
                    const m = mobs.find(mob => mob.id === zid);
                    return m && !m.isDead;
                });
                if (alive.length === 0) {
                    p.totpSecret = generateBase32Secret();
                    p.totpTimer = 60.0;
                    const client = getClientById(p.id);
                    if (client) client.send(JSON.stringify({ type: 'start_totp', secret: p.totpSecret }));
                }
            } else {
                p.totpTimer -= delta;
                if (p.totpTimer <= 0) {
                    fail2FAServer(p);
                }
            }
        }
    });

    prevTime = time;
    
    broadcast({
        type: 'update',
        players: Array.from(players.values()).map(p => ({
            id: p.id, x: p.x, y: p.y, z: p.z, yaw: p.yaw, dim: p.dim, username: p.username, mode: p.mode, health: p.health
        })),
        mobs: mobs.filter(m => {
            if (m.isDead) return false;
            // Aggressively cull static merchants to save server loop bandwidth!
            if (m.type === 'merchant') {
                for (let p of players.values()) {
                    if (p.dim === m.dim && Math.abs(p.x - m.x) < 250 && Math.abs(p.z - m.z) < 250) return true;
                }
                return false;
            }
            return true;
        }).map(m => ({
            id: m.id, type: m.type, x: m.x, y: m.y, z: m.z, dim: m.dim,
            lookAt: m.lookAt, health: m.health, naturalSpawn: m.naturalSpawn,
            isCharging: m.isCharging, archetype: m.archetype,
            explodeTimer: m.explodeTimer, eatenBlock: m.eatenBlock,
            isInvisible: m.isInvisible
        })),
        timeRatio: worldTime / DAY_DURATION,
        tps: currentTPS,
        tickTime: lastTickDuration
    });
    
    // Broadcast Projectiles separately to keep update packet clean
    if (projectiles.length > 0) {
        broadcast({
            type: 'projectile_update',
            projectiles: projectiles
        });
    }
    
    lastTickDuration = performance.now() - tickStart;
}, 50);

console.log("Server running on ws://localhost:8080");