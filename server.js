const WebSocket = require('ws');
const fs = require('fs');
const { spawn } = require('child_process');

const wss = new WebSocket.Server({host: '0.0.0.0', port: 25565 });

// --- SERVER WORLD STATE ---
const players = new Map(); 
const mobs = [];
const worldBlocks = new Map(); 
const villagePOIs = []; 
const projectiles = []; 
const spawners = []; 
let hostId = null;

// Anomaly State Tracking
let hostHTMLSnapshot = null;
let pendingSessions = new Map(); // sessionId -> Saved Player Data
let hostSessionId = null;

// Timing & Day/Night Cycle
let prevTime = performance.now();
let worldTime = 0;
const DAY_DURATION = 600; // Seconds for a full day/night cycle

// Config
const WORLD_SIZE = 40;
const BLOCK_SIZE = 5;

// Helper
const getKey = (x, y, z, dim) => `${Math.round(x)},${Math.round(y)},${Math.round(z)},${dim}`;

// Fluid Queue
const fluidQueue = new Set(); // Stores keys "x,y,z,dim" of blocks to update

// Unbreakable blocks in Survival
const UNBREAKABLE_BLOCKS = ['bedrock', 'end_frame', 'end_frame_filled', 'portal', 'nether_portal', 'network_block'];

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

function generateOverworld() {
    for (let x = -WORLD_SIZE/2; x < WORLD_SIZE/2; x++) {
        for (let z = -WORLD_SIZE/2; z < WORLD_SIZE/2; z++) {
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
    // Basement
    const by = cy - 12*BLOCK_SIZE;
    for(let dx=-3; dx<=3; dx++) {
        for(let dz=-3; dz<=3; dz++) {
            for(let dy=-1; dy<=4; dy++) {
                const wx = cx + dx*BLOCK_SIZE; const wy = by + dy*BLOCK_SIZE; const wz = cz + dz*BLOCK_SIZE;
                const k = getKey(wx, wy, wz, dim);
                if (worldBlocks.has(k)) worldBlocks.delete(k);
                
                if (dy === -1) { addBlock(wx, wy, wz, 'obsidian', dim); }
                else if (dy === 4 || Math.abs(dx) === 3 || Math.abs(dz) === 3) { addBlock(wx, wy, wz, 'stone', dim); }
            }
        }
    }
    // Shaft
    for(let dy=0; dy>=-12; dy--) {
        const wy = cy + dy*BLOCK_SIZE;
        const k = getKey(cx, wy, cz, dim);
        if (worldBlocks.has(k)) worldBlocks.delete(k);
    }
    // Safe landing
    addBlock(cx, cy - 11*BLOCK_SIZE, cz, 'water', dim, {level: 8});
    // Door
    addBlock(cx, by, cz - 2*BLOCK_SIZE, 'mysterious_door', dim, { open: false });
}

function generateIceSpikesBiome() {
    const offset = -100; 
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
    for(let z = -streetLength + 10; z <= streetLength - 10; z += step) {
        // Left Side
        if (Math.random() > 0.3) { 
            const type = Math.random() > 0.7 ? 'farm' : 'house'; 
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
    
    // Spawn villagers closer to center
    const count = 5 + Math.floor(Math.random() * 8);
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
    for(let y=1; y<=2; y++) {
        addBlock(cx, cy + y*BLOCK_SIZE, cz, 'nether_brick', dim);
    }
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
                
                // Spawn mob
                spawnMob(spawner.mobType, spawnX, spawner.y, spawnZ, spawner.dim);
                
                // Visual FX
                broadcast({ type: 'spawner_particles', x: spawner.x, y: spawner.y, z: spawner.z, dim: spawner.dim });
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
    if (Math.random() > 0.5) return; 
    console.log("Generating Lake...");

    const cx = (Math.random() - 0.5) * WORLD_SIZE * BLOCK_SIZE * 0.5;
    const cz = (Math.random() - 0.5) * WORLD_SIZE * BLOCK_SIZE * 0.5;
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
    }
}

function initWorld() {
    if (fs.existsSync('anomaly_server_state.json')) {
        console.log("Loading Anomalous Server State...");
        const state = JSON.parse(fs.readFileSync('anomaly_server_state.json', 'utf8'));
        
        state.blocks.forEach(b => worldBlocks.set(b.key, b.val));
        mobs.push(...state.mobs);
        state.players.forEach(p => pendingSessions.set(p.sessionId, p));
        hostSessionId = state.hostSessionId;
        worldTime = state.worldTime;
        hostHTMLSnapshot = state.hostHTMLSnapshot;
        
        fs.unlinkSync('anomaly_server_state.json');
    } else {
        console.log("Generating Server World...");
        generateOverworld();
        generateEndWorld();
        generateNether();
    }
}

function addBlock(x, y, z, type, dim, state = {}) {
    worldBlocks.set(getKey(x,y,z,dim), { type, state });
}

function spawnMob(type, x, y, z, dim) {
    let health = 3;
    if (type === 'villager') health = 5;
    if (type === 'end_crystal') health = 1;
    if (type === 'blaze') health = 20;
    if (type === 'pigman') health = 20;

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
        trades: type === 'villager' ? generateVillagerTrades() : [],
        // Blaze Specific
        chargeTick: 0,
        isCharging: false,
        shotsFired: 0,
        shotTimer: 0
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

function checkHazardDamage(entity) {
    // Determine "Feet" position based on entity type
    // Players (eye level y) need -10 offset. Mobs (feet level y) use y.
    let feetY = entity.y;
    if (entity.username) feetY = entity.y - 10;

    const bx = Math.round(entity.x / BLOCK_SIZE) * BLOCK_SIZE;
    const by = Math.round(feetY / BLOCK_SIZE) * BLOCK_SIZE;
    const bz = Math.round(entity.z / BLOCK_SIZE) * BLOCK_SIZE;

    // Check 3x3x3 volume around feet
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
                    if (type === 'magma' || type === 'cactus' || type === 'lava') {
                        // Calculate relative position to block center
                        const dx = Math.abs(entity.x - blockX);
                        const dz = Math.abs(entity.z - blockZ);
                        const dy = feetY - blockY; // Relative to feet

                        let hit = false;
                        
                        // Magma: Hot floor. Trigger if standing on top (dy ~ 5) or inside (dy ~ 0)
                        if (type === 'magma') {
                            if (dx < 4 && dz < 4) {
                                if (dy > -2 && dy < 6) hit = true;
                            }
                        }
                        // Cactus & Lava
                        else if (type === 'cactus' || type === 'lava') {
                            if (dx < 4 && dz < 4 && dy > -2 && dy < 6) hit = true;
                        }

                        if (hit) {
                            const now = performance.now();
                            if (now - (entity.lastDamageTime || 0) > 500) {
                                entity.health--;
                                if (entity.health <= 0) entity.isDead = true;
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
                    p.health = 20;
                    p.x = 0; p.y = 60; p.z = 0;
                    if (client) client.send(JSON.stringify({ type: 'respawn', x:0, y:60, z:0 }));
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

function attemptNaturalMobSpawning() {
    const timeRatio = (worldTime % DAY_DURATION) / DAY_DURATION;
    if (timeRatio < 0.5) return;
    if (mobs.filter(m=>!m.isDead).length > 50) return;

    if (Math.random() < 0.05) {
        const activePlayers = Array.from(players.values()).filter(p => p.dim === 'overworld');
        if (activePlayers.length === 0) return;

        const p = activePlayers[Math.floor(Math.random() * activePlayers.length)];
        
        const angle = Math.random() * Math.PI * 2;
        const dist = 15 * BLOCK_SIZE + Math.random() * 15 * BLOCK_SIZE;
        const sx = p.x + Math.cos(angle) * dist;
        const sz = p.z + Math.sin(angle) * dist;

        let spawnY = -1000;
        const checkX = Math.round(sx / BLOCK_SIZE) * BLOCK_SIZE;
        const checkZ = Math.round(sz / BLOCK_SIZE) * BLOCK_SIZE;

        for(let y=30 * BLOCK_SIZE; y > -10 * BLOCK_SIZE; y-=BLOCK_SIZE) {
             const blockData = worldBlocks.get(getKey(checkX, y, checkZ, 'overworld'));
             if (blockData && blockData.type !== 'air') {
                 spawnY = y + BLOCK_SIZE;
                 break;
             }
        }

        if (spawnY > -900) {
            const newMob = spawnMob('zombie', checkX, spawnY, checkZ, 'overworld');
            // Tag this mob as a natural night spawn
            newMob.naturalSpawn = true;
        }
    }
}

// --- SERVER-SIDE VILLAGER AI ---
function updateVillagerAI(mob, delta, timeRatio) {
    // Only AI for villagers in overworld
    if (mob.type !== 'villager' || mob.dim !== 'overworld') return;

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
            for (let y = by - BLOCK_SIZE; y > -101; y -= BLOCK_SIZE) {
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
    const timeRatio = (worldTime % DAY_DURATION) / DAY_DURATION;
    worldTime += delta;
    if (worldTime >= DAY_DURATION) worldTime = 0;

    attemptNaturalMobSpawning();

    // ... (Player hazard check code) ...
    players.forEach(p => {
        if (p.mode === 'survival') {
            if (checkHazardDamage(p)) {
                const client = getClientById(p.id);
                if (client) client.send(JSON.stringify({ type: 'damage', health: p.health }));
                if (p.health <= 0) {
                    p.health = 20;
                    p.x=0; p.y=60; p.z=0;
                    if (client) client.send(JSON.stringify({ type: 'respawn', x:0, y:60, z:0 }));
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
            players.forEach(pl => {
                if (pl.mode === 'survival' && pl.dim === p.dim) {
                    const dist = Math.hypot(p.x - pl.x, p.y - (pl.y+3), p.z - pl.z); // Center mass
                    if (dist < 4) {
                        hit = true;
                        pl.health -= 5; // 2.5 Hearts
                         const client = getClientById(pl.id);
                        if (client) client.send(JSON.stringify({ type: 'damage', health: pl.health }));
                        if (pl.health <= 0) {
                            pl.health = 20; pl.x=0; pl.y=60; pl.z=0;
                            if (client) client.send(JSON.stringify({ type: 'respawn', x:0, y:60, z:0 }));
                        }
                    }
                }
            });
        }

        if (hit || p.life <= 0) {
            projectiles.splice(i, 1);
        }
    }

    mobs.forEach(mob => {
        if (mob.isDead) return;
        if (mob.type === 'end_crystal') return;
        
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
             players.forEach(p => {
                 if (p.dim === mob.dim && p.mode === 'survival') {
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
        if (mob.type === 'villager') updateVillagerAI(mob, delta, timeRatio);

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
        if (isDay && mob.type === 'zombie' && mob.naturalSpawn && mob.dim === 'overworld') {
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
        
        let groundY = -101;
        const bx = Math.round(mob.x/5)*5;
        const bz = Math.round(mob.z/5)*5;
        for(let y=Math.floor(mob.y/5)*5; y>-50; y-=5) {
             const kKey = getKey(bx,y,bz,mob.dim);
             const blockData = worldBlocks.get(kKey);
             if (blockData && blockData.type !== 'air' && blockData.type !== 'crop' && blockData.type !== 'water') {
                 groundY = y + 5; 
                 break;
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

        if (mob.type === 'zombie') {
            // 1. PANIC CHECK: Am I stuck inside a house?
            // If the zombie is under a roof, forced glitch-out (Reverse velocity violently)
            if (Math.random() < 0.1 && isLocationIndoors(mob.x, mob.y, mob.z, mob.dim)) {
                 mob.vx = (Math.random() - 0.5) * 30; // Random panic movement
                 mob.vz = (Math.random() - 0.5) * 30;
                 target = null; // Ignore targets while panicking
            } else {
                // Normal Targeting
                mobs.forEach(other => {
                    if (other.type === 'villager' && !other.isDead && other.dim === mob.dim) {
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

                players.forEach(p => {
                    if (p.mode === 'survival' && p.dim === mob.dim) {
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

        // COMMON ATTACK LOGIC (Zombie & Pigman)
        if (minDist < 8 && target && victim) {
            const now = performance.now();
            if (now - (mob.lastAttackTime || 0) > 1000) {
                // Damage calculation
                let dmg = 1;
                if (mob.type === 'pigman') dmg = 3; // Gold sword deals more damage

                victim.health -= dmg;
                mob.lastAttackTime = now;
                
                if (isPlayer) {
                    const client = getClientById(victim.id);
                    if (client) client.send(JSON.stringify({ type: 'damage', health: victim.health }));
                    
                    if (victim.health <= 0) {
                        victim.health = 20;
                        victim.x = 0; victim.y = 60; victim.z = 0; 
                        if (client) client.send(JSON.stringify({ type: 'respawn', x:0, y:60, z:0 }));
                    }
                } else {
                    if (victim.health <= 0) victim.isDead = true;
                    broadcast({ type: 'entity_update', mob: victim });
                }
            }
            // Stop moving when attacking
            mob.vx = 0; mob.vz = 0;
        }

        // Apply Movement & Avoidance (Zombie & Pigman)
        const isKnockedBack = Math.abs(mob.vx) > 50 || Math.abs(mob.vz) > 50;
        if (target && (mob.type === 'zombie' || mob.type === 'pigman') && !isKnockedBack) {
            mob.lookAt = {x: target.x, y: mob.y, z: target.z};
            const dx = target.x - mob.x;
            const dz = target.z - mob.z;
            const len = Math.hypot(dx, dz);
            if (len > 0.1) { 
                const speed = 15;
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
        } else if (mob.type === 'zombie' || mob.type === 'pigman') {
            // Friction
            if (isKnockedBack) {
                mob.vx -= mob.vx * 2.0 * delta;
                mob.vz -= mob.vz * 2.0 * delta;
            } else {
                mob.vx *= 0.9;
                mob.vz *= 0.9;
            }
        }

        if (mob.y < -100) mob.isDead = true;
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

function getStarterInventory() {
    return {
        'grass': 0, 'dirt': 10, 'stone': 10, 'wood': 10, 
        'leaves': 0, 'sand': 0, 'cactus': 0, 
        'end_frame': 0, 'eye_of_ender': 0, 'end_stone': 0, 
        'emerald': 0,
        // --- NEW: Fix for collecting ice/snow ---
        'packed_ice': 0,
        'snow_block': 0,
        'netherrack': 0, 'glowstone': 0, 'flint_and_steel': 1,
        'blaze_rod': 0, 'nether_brick': 0, 'spawner': 0,
        'quartz_ore': 0, 'magma': 0, 'red_mushroom': 0, 'quartz': 0, 'gold_nugget': 0,
        'hammer': 1, 'mysterious_door': 0
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
        health: 20, maxHealth: 20, inventory: getStarterInventory(), lastDamageTime: 0
    };
    players.set(id, initialPlayer);

    ws.on('message', msg => {
        try {
            const d = JSON.parse(msg);
            let p = players.get(id);
            
            if(d.type === 'join') {
                // Check if this is a reconnecting client post-anomaly
                if (d.sessionId && pendingSessions.has(d.sessionId)) {
                    const savedPlayer = pendingSessions.get(d.sessionId);
                    savedPlayer.id = id;
                    savedPlayer.username = d.username;
                    players.set(id, savedPlayer);
                    pendingSessions.delete(d.sessionId);
                    p = savedPlayer; // Update reference
                    
                    if (hostSessionId === d.sessionId) hostId = id;
                    console.log(`${d.username} reconnected to anomalous reality.`);
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
            }

            if(d.type === 'move') { 
                if(p) { p.x=d.x; p.y=d.y; p.z=d.z; p.yaw=d.yaw; p.dim=d.dim; } 
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
                
                // Register Spawner if placed by player
                if (d.blockType === 'spawner') {
                    spawners.push({ x: d.x, y: d.y, z: d.z, dim: d.dim, timer: 0, mobType: 'blaze' });
                }

                if(d.blockType === 'end_frame_filled') checkPortalServer(d.x, d.y, d.z, d.dim);

                // SCHEDULE FLUID UPDATE
                if (d.blockType === 'water' || d.blockType === 'lava') scheduleFluidUpdate(d.x, d.y, d.z, d.dim); 
                wakeNeighbors(d.x, d.y, d.z, d.dim); 
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
                        return;
                    }

                    if (p.mode === 'survival') {
                        let drop = existingType;
                        if (drop === 'end_frame_filled') drop = 'end_frame'; 
                        if (drop === 'quartz_ore') drop = 'quartz'; // Drop item
                        
                        if (p.inventory[drop] !== undefined) {
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
                const mob = mobs.find(m => m.id === d.mob);
                if (mob) {
                    if (mob.type === 'end_crystal') {
                        mob.isDead = true;
                        broadcast({ type:'entity_update', mob });
                        createExplosion(mob.x, mob.y, mob.z, mob.dim, 6);
                    } else {
                        mob.health--;
                        
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
                                ws.send(JSON.stringify({ type: 'inventory_update', inventory: p.inventory }));
                            }
                        }
                        broadcast({ type:'entity_update', mob });
                    }
                } else {
                    const targetPlayer = players.get(d.mob);
                    if (targetPlayer && targetPlayer.mode === 'survival') {
                        targetPlayer.health--;
                        
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
                            targetPlayer.health = 20;
                            targetPlayer.x = 0; targetPlayer.y = 60; targetPlayer.z = 0; 
                            if (victimClient) victimClient.send(JSON.stringify({ type: 'respawn', x:0, y:60, z:0 }));
                        }
                    }
                }
            }

            // --- PLAYER INTERACTS WITH ENTITY ---
            if (d.type === 'entity_interact') {
                if (p.mode !== 'survival') return;

                const targetMob = mobs.find(m => m.id === d.targetId);
                
                if (targetMob && !targetMob.isDead && targetMob.type === 'villager' && targetMob.dim === p.dim) {
                    const dist = Math.hypot(p.x - targetMob.x, p.y - targetMob.y, p.z - targetMob.z);
                    if (dist < 5 * BLOCK_SIZE) {
                        // Mark villager as busy
                        targetMob.tradingWith = id; // <-- NEW
                        
                        ws.send(JSON.stringify({ 
                            type: 'open_trade', 
                            trades: targetMob.trades, 
                            traderId: targetMob.id 
                        }));
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
                if (dist > 10) {
                     ws.send(JSON.stringify({ type: 'trade_fail' }));
                     return;
                }

                const trade = targetMob.trades[d.tradeIndex];
                
                // Validate inventory
                const currentStock = p.inventory[trade.costItem] || 0;
                if (currentStock >= trade.costCount) {
                    // Execute Trade
                    p.inventory[trade.costItem] -= trade.costCount;
                    p.inventory[trade.rewardItem] = (p.inventory[trade.rewardItem] || 0) + trade.rewardCount;
                    
                    ws.send(JSON.stringify({ type: 'inventory_update', inventory: p.inventory }));
                    ws.send(JSON.stringify({ type: 'trade_success' }));
                } else {
                    ws.send(JSON.stringify({ type: 'trade_fail' }));
                }
            }

            // --- HOST TOGGLES GAMEMODE ---
            if (d.type === 'admin_gamemode_toggle') {
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
                        const stateToSave = {
                            blocks: Array.from(worldBlocks.entries()).map(([k, v]) => ({ key: k, val: v })),
                            mobs: mobs,
                            players: Array.from(players.values()),
                            hostSessionId: players.get(hostId)?.sessionId,
                            worldTime: worldTime,
                            hostHTMLSnapshot: clientRes.patched
                        };
                        fs.writeFileSync('anomaly_server_state.json', JSON.stringify(stateToSave));
                        
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
                        console.log("Rebooting server into anomalous reality...");
                        const child = spawn(process.argv[0], ['temp_server.js'], { detached: true, stdio: 'inherit' });
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

setInterval(() => {
    const time = performance.now();
    const delta = (time - prevTime) / 1000;
    if (delta > 1.0) { prevTime = time; return; } 
    
    updateMobs(delta);

    // Run fluid sim every tick (or throttle if needed)
    updateFluids(delta);

    // Update Spawners
    updateSpawners(delta);

    prevTime = time;
    
    broadcast({
        type: 'update',
        players: Array.from(players.values()),
        mobs: mobs.filter(m => !m.isDead),
        timeRatio: worldTime / DAY_DURATION 
    });
    
    // Broadcast Projectiles separately to keep update packet clean
    if (projectiles.length > 0) {
        broadcast({
            type: 'projectile_update',
            projectiles: projectiles
        });
    }
}, 50);
