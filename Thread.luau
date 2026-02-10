local LoopController = {}
LoopController.__index = LoopController

local ThreadController = setmetatable({}, LoopController)
ThreadController.__index = ThreadController
LoopController.Thread = ThreadController

function LoopController.new()
    local self = setmetatable({}, LoopController)
    self.Heartbeat = game:GetService("RunService").Heartbeat
    self.Threads = {}
    self.Active = true
    self.Connection = self.Heartbeat:Connect(function()
        if not self.Active then return end
        for i = #self.Threads, 1, -1 do
            local thread = self.Threads[i]
            if thread then thread:handle() end
        end
    end)
    return self
end

function LoopController:newThread(...)
    local thread = ThreadController.new(...)
    self.Threads[#self.Threads + 1] = thread
    return thread
end

function LoopController:removeThread(threadController)
    local idx = table.find(self.Threads, threadController)
    if idx then
        threadController:Disable()
        table.remove(self.Threads, idx)
    end
end

function LoopController:Destroy()
    self.Active = false
    self.Connection:Disconnect()
    for _, thread in ipairs(self.Threads) do
        thread:Disable()
    end
    table.clear(self.Threads)
end

function ThreadController.new(rate, func, repeatTimes)
    local self = setmetatable({}, ThreadController)
    self.Rate = rate or 0
    self.finished = 0
    self.repeatTimes = repeatTimes
    self.MainFunction = func
    self.Disabled = false
    self.Status = "idle"

    self._execute = function()
        self.Status = "running"
        local ok, err = pcall(func)  -- no colon, no accidental self injection
        if not ok then
            warn("[ThreadController] Execution error:", err)
        end
        task.wait(self.Rate)
        self:Finish()
    end

    self.MainThread = coroutine.create(self._execute)
    task.spawn(self.MainThread)
    return self
end

function ThreadController:handle()
    if self.Disabled then return end

    if self.repeatTimes and self.finished >= self.repeatTimes then
        self:Disable()
        return
    end

    local state = coroutine.status(self.MainThread)

    if state == "dead" and self.Status == "finished" then
        self.Status = "idle"
        self.MainThread = coroutine.create(self._execute)
        task.spawn(self.MainThread)
    end
end

function ThreadController:Finish()
    self.finished += 1
    self.Status = "finished"
end

function ThreadController:Disable()
    if self.Disabled then return end
    self.Disabled = true
    local state = coroutine.status(self.MainThread)
    if state ~= "dead" then
        pcall(task.cancel, self.MainThread)
    end
end

return LoopController
